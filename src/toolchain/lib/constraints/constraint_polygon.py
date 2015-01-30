from constraint_generation import *
from data.constraint import Constraint
from sympy.polys.polytools import Poly
from shapely.geometry import Polygon, LineString

class ConstraintPolygon(ConstraintGeneration):

    def __init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc):
        ConstraintGeneration.__init__(self, samples, parameters, threshold, safe_above_threshold, threshold_area, _smt2interface, _ratfunc)

        self.best_polygon = None
        self.safe = None

    def change_current_constraint(self):
        # change current constraint to avoid memout in smt
        # returns (new_constraint, new_covered_area, area_safe)

        #TODO inform user
        return (new_constraints, self.best_polygon, self.safe)

    def finalize_step(self, new_constraints):
        # Plot polygon
        if self.safe:
            self.plot_results(additional_polygons_green = [self.best_polygon], display = True)
        else:
            self.plot_results(additional_polygons_red = [self.best_polygon], display = True)

    def next_constraint(self):
        #TODO input comes from user
        return

    def add_polygon(self, polygon, safe):
        """Extends the current area by using the new polygon
        polygon marks the new area to cover
        safe indicates whether the area is safe or bad
        returns tuple (valid constraint, polygon/counterexample point)
        if constraint is valid the tuple  is (True, polygon added)
        if constraint is invalid the tuple is (False, point as counterexample)
        """
        self.best_polygon = polygon
        self.safe = safe
        new_constraints = self.compute_constraints(polygon)
        result = self.analyze_constraint(new_constraints, polygon, safe)
        return result