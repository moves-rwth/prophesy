from regions.region_checker import RegionChecker, RegionCheckResult
from shapely.geometry.polygon import Polygon, orient, LinearRing
from sympy.polys.polytools import Poly

import smt.smt

from data.hyperrectangle import HyperRectangle
from data.interval import Interval, BoundType
from data.constraint import Constraint, ComplexConstraint

import time




class SmtRegionChecker(RegionChecker):
    def __init__(self, smt2interface, parameters, ratfunc):
        self._smt2interface = smt2interface
        self._parameters = parameters
        self._ratfunc = ratfunc

        self.benchmark_output = []

    def _symbols(self):
        return list([x[0] for x in self._parameters])

    def _intervals(self):
        return list([x[1] for x in self._parameters])

    def print_info(self):
        i = 1
        print("no.  result   time  tot. time   area  tot. area")
        total_sec = 0
        total_area = 0
        for benchmark in self.benchmark_output:
            total_sec = total_sec + benchmark[1]
            if benchmark[0] == smt.smt.Answer.unsat:
                total_area = total_area + benchmark[2]
            print("{:3}   {:>6s}  {:5.2f}     {:6.2f}  {:4.3f}      {:4.3f}".format(i, benchmark[0].name, benchmark[1], total_sec, benchmark[2], total_area))
            i = i + 1


    def _compute_constraint(self, polygon):
        """Compute regions from polygon (Polygon, LineString or LinearRing)
        Area will be considered at the rhs (ccw) of line segments
        :param polygon: must be convex
        :return: single (Complex)Constraint describing the polygon
        """
        if isinstance(polygon, HyperRectangle):
            constraint = Constraint(Poly(0, self._symbols()), "=", self._symbols())
            for parameter, interval in zip(self._symbols(), polygon.intervals):
                constraint = constraint & Constraint(Poly(parameter-interval.left_bound(), self._symbols()), (">=" if interval.left_bound_type() == BoundType.closed else ">") , self._symbols())
                constraint = constraint & Constraint(Poly(parameter-interval.right_bound(), self._symbols()), ("<=" if interval.left_bound_type() == BoundType.closed else "<") , self._symbols())
            return constraint

        if isinstance(polygon, LinearRing):
            # Convert to polygon so it can be oriented
            polygon = Polygon(polygon)

        if isinstance(polygon, Polygon):
            assert len(list(polygon.interiors)) == 0
            polygon = orient(polygon, sign=1.0)
            polygon = polygon.exterior
        points = list(polygon.coords)
        assert len(points) >= 2

        constraint = None
        # Calculate half-plane for each pair of points
        # http://math.stackexchange.com/questions/82151/find-the-equation-of-the-plane-passing-through-a-point-and-a-vector-orthogonal
        for p1, p2 in zip(points[:-1], points[1:]):
            # Get vector direction (parallel to hyperplane)
            dvec = tuple([c2 - c1 for c1, c2 in zip(p1, p2)])
            # Make vector orthogonal to hyperplane
            # NOTE: rotate clockwise
            # TODO: 2D only
            dvec = (dvec[1], -dvec[0])

            # Constant is dot-product of directional vector and origin
            c = sum([c1 * c2 for c1, c2 in zip(dvec, p1)])
            # Construct polynomial for line
            poly = Poly(-c, self._symbols())
            for parameter, coefficient in zip(self._symbols(), dvec):
                if coefficient != 0:
                    poly = Poly(poly + parameter * coefficient, self._symbols())

            # TODO: '<=' as polygon is CCW oriented, not sure if this applies to n-dimen
            new_constraint = Constraint(poly, "<=", self._symbols())
            if constraint is None:
                constraint = new_constraint
            else:
                constraint = constraint & new_constraint

        # print("constraint: {0}".format(constraint))
        return constraint

    def analyse_region(self, polygon, safe):
        """Extends the current area by using the new polygon
        regions are the newly added regions for the polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        """
        smt_successful = False
        smt_model = None

        constraint = self._compute_constraint(polygon)

        while not smt_successful:
            # check constraint with smt
            with self._smt2interface as smt_context:
                #print("Checking constraint {}".format(constraint))
                smt_context.assert_constraint(constraint)

                smt_context.set_guard("safe", not safe)
                smt_context.set_guard("bad", safe)
                #print("Calling smt solver")
                start = time.time()
                checkresult = smt_context.check()
                duration = time.time() - start
                #print("Call took {0} seconds".format(duration))
                if isinstance(polygon, HyperRectangle):
                    self.benchmark_output.append((checkresult, duration, polygon.size()))
                else:
                    self.benchmark_output.append((checkresult, duration, polygon.area))
                #self.print_benchmark_output(self.benchmark_output)
                if not checkresult in [smt.smt.Answer.sat, smt.smt.Answer.unsat]:
                    # smt call not finished -> change constraint to make it better computable
                    # TODO what to do in GUI?
                    #print("{}: Change constraint for better computation".format(checkresult))
                    break
                else:
                    smt_successful = True
                    if checkresult == smt.smt.Answer.sat:
                        smt_model = smt_context.get_model()
                    break

        if checkresult == smt.smt.Answer.unsat:
            return RegionCheckResult.unsat, None
        elif checkresult == smt.smt.Answer.sat:
            # add new point as counter example to existing regions
            model_point = ()
            for p in self._symbols():
                if p.name in smt_model:
                    model_point = model_point + (smt_model[p.name],)
                else:
                    # if parameter is undefined set as 0.5
                    #TODO more is possible here.
                    model_point = model_point + (0.5,)
                    smt_model[p.name] = 0.5
            value = self._ratfunc.subs(smt_model.items()).evalf()
            return RegionCheckResult.sat, (model_point, value)
        else:
            # SMT failed completely
            return RegionCheckResult.unknown, None




    @classmethod
    def is_point_fulfilling_constraint(cls, pt, constraint):
        """Check whether the given point is satisfied by the regions
        (i.e. is contained by it)"""
        if isinstance(constraint, ComplexConstraint):
            if constraint.operator == "or":
                return any([cls.is_point_fulfilling_constraint(pt, sub_constraint) for sub_constraint in constraint.constraints])
            elif constraint.operator == "and":
                return all([cls.is_point_fulfilling_constraint(pt, sub_constraint) for sub_constraint in constraint.constraints])
            else:
                assert False, "Unknown constraint operator {}".format(constraint.operator)

        pol = constraint.polynomial.eval({x: y for x, y in zip(constraint.symbols, pt)}).evalf()

        if constraint.relation == "=":
            return abs(pol) < config.PRECISION
        elif constraint.relation == "<":
            return pol < 0
        elif constraint.relation == ">":
            return pol > 0
        elif constraint.relation == "<=":
            return pol <= 0
        elif constraint.relation == ">=":
            return pol >= 0
        elif constraint.relation == "<>":
            return abs(pol) > config.PRECISION
