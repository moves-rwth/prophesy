import os
import shutil
import tempfile
import logging
from abc import ABCMeta, abstractmethod

from prophesy.regions.region_checker import RegionCheckResult

import shapely.geometry

from prophesy.data.hyperrectangle import HyperRectangle

from prophesy.output.plot import Plot
from prophesy.util import ensure_dir_exists
from prophesy.config import configuration
from prophesy.exceptions.module_error import ModuleError


class RegionGenerator:
    """A generator for regions. 
    This class acts as an iterable that generates new regions (or counterexamples),
     until the search space is exhausted (which possibly never happens)"""
    __metaclass__ = ABCMeta

    def __init__(self, samples, parameters, threshold, threshold_area, checker, _ratfunc):
        if len(parameters) != 2:
            raise NotImplementedError

        self.samples = samples.copy()
        self.parameters = parameters
        self.threshold = threshold
        self.threshold_area = threshold_area

        self.max_area_sum = HyperRectangle(*self.parameters.get_variable_bounds()).size()

        self.checker = checker
        self.ratfunc = _ratfunc

        # Stores all regions as triple ([constraint], polygon representation, bad/safe)
        self.all_polys = []
        self.safe_polys = []
        self.bad_polys = []
        self.new_samples = {}

        self.plot = True
        self.first_pdf = True
        ensure_dir_exists(configuration.get_plots_dir())
        _, self.result_file = tempfile.mkstemp(suffix=".pdf", prefix="result_", dir=configuration.get_plots_dir())

    def __iter__(self):
        # Prime the generator
        return next(self)

    def __next__(self):
            # get next constraint depending on algorithm
            result_constraint = self.next_constraint()
            while result_constraint is not None:
                polygon, area_safe = result_constraint
                result = self._analyse_region(polygon, area_safe)
                if result is None:
                    # End of generator
                    return
                yield result

                # get next constraint depending on algorithm
                result_constraint = self.next_constraint()

    def _add_pdf(self, name):
        """
        Adds pdf with name to result.pdf in tmp directory
        """
        #TODO Only do this if the option is installed.
        if not configuration.is_module_available("pypdf2"):
            raise ModuleError("Module pypdf2 is needed for using the pdf export for regions. Maybe your config is oudated?")
        from PyPDF2 import PdfFileMerger, PdfFileReader

        if self.first_pdf:
            self.first_pdf = False
            shutil.copyfile(name, self.result_file)
            logging.info("Plot file located at {0}".format(self.result_file))
        else:
            merger = PdfFileMerger()
            merger.append(PdfFileReader(self.result_file, 'rb'))
            merger.append(PdfFileReader(name, 'rb'))
            merger.write(self.result_file)


    def plot_candidate(self):
        pass

    def plot_results(self, *args, **kwargs):
        if not self.plot:
            return
        # Extend arguments
        poly_green = kwargs.get('poly_green', [])
        kwargs['poly_green'] = poly_green + self.safe_polys
        poly_red = kwargs.get('poly_red', [])
        kwargs['poly_red'] = poly_red + self.bad_polys

        # Split samples appropriately
        samples_green, samples_red = self.samples.split(self.threshold)
        samples_green = [res.instantiation.get_point(self.parameters) for res in samples_green.instantiation_results()]
        samples_red = [res.instantiation.get_point(self.parameters) for res in samples_red.instantiation_results()]

        _, result_tmp_file = tempfile.mkstemp(".pdf", dir=configuration.get_plots_dir())
        Plot.plot_results(parameters=self.parameters,
                          samples_green=samples_green,
                          samples_red=samples_red,
                          path_to_save=result_tmp_file,
                          *args, **kwargs)
        self._add_pdf(result_tmp_file)
        os.unlink(result_tmp_file)

    def is_inside_polygon(self, point, polygon):
        # checks if the point lies inside the polygon
        return point.within(polygon) or point.touches(polygon)

    def intersects(self, polygon1, polygon2):
        """checks if two polygons intersect, touching is okay"""
        #TODO first check bounding boxes?
        return polygon1.intersects(polygon2) and not polygon1.touches(polygon2)

    @abstractmethod
    def refine_with_intersections(self, polygon):
        """Compute the intersections of the polygon with the existing ones
        and refine it by getting the difference
        returns the refined polygon"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def next_constraint(self):
        """Generate a new set of regions ([regions], area, area_safe),
        where [regions] is a list of Constraint, area is a polygon representation of the new area
        and area_safe indicated whether the area should be determined safe (or not)"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def fail_constraint(self, constraint, safe):
        """Update current set of regions, usually to avoid mem or time out.
        Returns same as next_constraint"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def reject_constraint(self, constraint, safe, sample):
        """Called for a constraint that is rejected (sample found).
        @param constraint Polygon or HyperRectangle
        @param safe Boolean
        @param sample Sample
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def accept_constraint(self, constraint, safe):
        """Called for a constraint that is accepted (i.e. unsat)"""
        raise NotImplementedError("Abstract parent method")


    def _area(self, pol):
        if isinstance(pol, shapely.geometry.Polygon):
            return pol.area
        if isinstance(pol, HyperRectangle):
            return pol.size()
        assert False


    def generate_constraints(self, max_iter=-1, max_area=1):
        """Iteratively generates new regions, heuristically, attempting to
        find the largest safe or unsafe area
        max_iter: Number of regions to generate/check at most (not counting SMT failures),
        -1 for unbounded"""
        if max_iter == 0:
            return self.safe_polys, self.bad_polys, self.new_samples

        for result in self:
            res_status, data = result
            if res_status == RegionCheckResult.unsat :
                self.all_polys.append(data)
                poly, safe = data
                if safe:
                    self.safe_polys.append(poly)
                else:
                    self.bad_polys.append(poly)
            elif res_status == RegionCheckResult.sat:
                pass

            area_sum = sum(self._area(poly) for poly, safe in self.all_polys)
            if area_sum > max_area * self.max_area_sum:
                break

            max_iter -= 1
            if max_iter == 0:
                break

            # Plot intermediate result
            if len(self.all_polys) % 4 == 0:
                self.plot_results(display=False)

        # Plot the final outcome
        if self.plot:
            self.plot_results(display=False)
            logging.info("Generation complete, plot located at {0}".format(self.result_file))
        self.checker.print_info()

        return self.safe_polys, self.bad_polys, self.new_samples

    def _analyse_region(self, polygon, safe):
        checkresult, additional = self.checker.analyse_region(polygon, safe)
        if checkresult == RegionCheckResult.unsat:
            # remove unnecessary samples which are covered already by regions
            for pt in list(self.samples.keys()):
                if isinstance(polygon, HyperRectangle):
                    if polygon.contains(pt):
                        del self.samples[pt]
                else:
                    if shapely.geometry.Point(*pt).within(polygon):
                        del self.samples[pt]

            # update everything in the algorithm according to correct new area
            self.accept_constraint(polygon, safe)
            return checkresult, (polygon, safe)
        elif checkresult == RegionCheckResult.sat:
            # add new point as counter example to existing regions
            self.samples.add_sample(additional)
            self.reject_constraint(polygon, safe, additional)
            return checkresult, (additional, safe)
        else:
            result_update = self.fail_constraint(polygon, safe)
            return checkresult, result_update
