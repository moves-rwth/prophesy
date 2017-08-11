import os
import shutil
import tempfile
import logging
import shapely.geometry
from abc import ABCMeta, abstractmethod

from prophesy.regions.region_checker import RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.output.plot import Plot
from prophesy.util import ensure_dir_exists
from prophesy.config import configuration
from prophesy.exceptions.module_error import ModuleError

from prophesy.regions.welldefinedness import WelldefinednessResult


class RegionGenerator:
    """
    A generator for regions. 
    This class acts as an iterable that generates new regions (or counterexamples),
    until the search space is exhausted (which possibly never happens)\
    """
    __metaclass__ = ABCMeta

    def __init__(self, samples, parameters, threshold, checker, wd_constraints, gp_constraints):
        self.safe_samples, self.bad_samples, self.illdefined_samples = samples.copy().split(threshold)
        self.parameters = parameters
        self.threshold = threshold

        self.max_area_sum = HyperRectangle(*self.parameters.get_variable_bounds()).size()

        self.checker = checker

        # Stores all regions as triple ([constraint], polygon representation, bad/safe)
        self.all_polys = []
        self.safe_polys = []
        self.bad_polys = []
        self.illdefined_polys = []
        self.new_samples = {}
        self.wd_constraints = wd_constraints
        self.gp_constraints = gp_constraints

        self._plot_candidates = False
        self.plot = len(self.parameters) <= 2
        self.first_pdf = True
        ensure_dir_exists(configuration.get_plots_dir())
        _, self.result_file = tempfile.mkstemp(suffix=".pdf", prefix="result_", dir=configuration.get_plots_dir())

    def __iter__(self):
        # Prime the generator
        return next(self)

    def __next__(self):
        result_constraint = self.next_region()
        while result_constraint is not None:
            polygon, welldefined, area_safe = result_constraint
            if self._plot_candidates:
                self.plot_candidate()
            if welldefined == WelldefinednessResult.Illdefined:
                self.ignore_region()
                yield WelldefinednessResult.Illdefined, polygon
            else:
                result = self._analyse_region(polygon, welldefined, area_safe)
                if result is None:
                    # End of generator
                    return
                yield result

            # get next constraint depending on algorithm
            result_constraint = self.next_region()

    def _add_pdf(self, name):
        """
        Adds pdf with name to result.pdf in tmp directory
        """
        # TODO Only do this if the option is installed.
        if not configuration.is_module_available("pypdf2"):
            raise ModuleError(
                "Module pypdf2 is needed for using the pdf export for regions. Maybe your config is oudated?")
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
        poly_black = kwargs.get('poly_black', [])
        kwargs['poly_black'] = poly_black + self.illdefined_polys

        # Split samples appropriately
        samples_green = [res.instantiation.get_point(self.parameters) for res in
                         self.safe_samples.instantiation_results()]
        samples_red = [res.instantiation.get_point(self.parameters) for res in self.bad_samples.instantiation_results()]

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
        # TODO first check bounding boxes?
        return polygon1.intersects(polygon2) and not polygon1.touches(polygon2)

    @abstractmethod
    def refine_with_intersections(self, polygon):
        """Compute the intersections of the polygon with the existing ones
        and refine it by getting the difference
        returns the refined polygon"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def next_region(self):
        """Generate a new set of regions"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def fail_region(self, region, safe):
        """Update current set of regions, usually to avoid mem or time out.
        Returns same as next_constraint"""
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def reject_region(self, region, safe, sample):
        """Called for a constraint that is rejected (sample found).
        
        :param constraint: Polygon or HyperRectangle
        :param safe: Boolean
        :param sample: Sample
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def ignore_region(self):
        """
        Region is overall ill-defined, skip it
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def accept_region(self):
        """Called for a constraint that is accepted"""
        raise NotImplementedError("Abstract parent method")

    def _area(self, pol):
        if isinstance(pol, shapely.geometry.Polygon):
            return pol.area
        if isinstance(pol, HyperRectangle):
            return pol.size()
        assert False

    def generate_constraints(self, max_iter=-1, max_area=1, plot_every_n=1, plot_candidates=True):
        """Iteratively generates new regions, heuristically, attempting to
        find the largest safe or unsafe area
        
        :param max_iter: Number of regions to generate/check at most (not counting SMT failures),
        -1 for unbounded
        :param max_area: Maximal area that should be covered.
        :param plot_every_n: How often should the plot be appended to the pdf.
        :param plot_candidates: True, iff candidates should be plotted
        """
        if max_iter == 0:
            return self.safe_polys, self.bad_polys, self.new_samples

        self._plot_candidates = plot_candidates

        for result in self:
            res_status, data = result
            if res_status == WelldefinednessResult.Illdefined:
                self.all_polys.append((data,WelldefinednessResult.Illdefined))
                self.illdefined_polys.append(data)
            elif res_status == RegionCheckResult.Satisfied:
                self.all_polys.append(data)
                poly, safe = data
                if safe:
                    self.safe_polys.append(poly)
                else:
                    self.bad_polys.append(poly)
            elif res_status == RegionCheckResult.CounterExample:
                pass
            elif res_status == RegionCheckResult.Refined:
                raise NotImplementedError("We have to record the refinement.")
                # self.all_polys.append()
            elif res_status == RegionCheckResult.unknown:
                pass
            else:
                assert False  # All options should be covered by switching if/else

            area_sum = sum(self._area(poly) for poly, safe in self.all_polys)
            if area_sum > max_area * self.max_area_sum:
                break

            max_iter -= 1
            if max_iter == 0:
                break

            # Plot intermediate result
            if res_status != RegionCheckResult.unknown and len(self.all_polys) % plot_every_n == 0:
                self.plot_results(display=False)

        # Plot the final outcome
        if self.plot:
            self.plot_results(display=False)
            logging.info("Generation complete, plot located at {0}".format(self.result_file))
        self.checker.print_info()

        return self.safe_polys, self.bad_polys, self.new_samples

    def _analyse_region(self, polygon, welldefined, safe):
        assert welldefined == WelldefinednessResult.Welldefined
        checkresult, additional = self.checker.analyse_region(polygon, safe)
        if checkresult == RegionCheckResult.Satisfied:
            # remove unnecessary samples which are covered already by regions
            # TODO region might contain this info, why not use that.
            self.safe_samples = self.safe_samples.filter_instantiation(
                lambda x: not polygon.contains(x.get_point(self.parameters)))
            self.bad_samples = self.bad_samples.filter_instantiation(
                lambda x: not polygon.contains(x.get_point(self.parameters)))

            # TODO make the code above work with the polygons, as below.
            # for instantiation, _ in self.samples:
            #        if shapely.geometry.Point(*pt).within(polygon):
            #            del self.samples[pt]

            # update everything
            self.accept_region()
            return checkresult, (polygon, safe)
        elif checkresult == RegionCheckResult.CounterExample:
            # add new point as counter example to existing regions
            if additional.result >= self.threshold:
                self.safe_samples.add_result(additional)
            else:
                self.bad_samples.add_result(additional)
            self.reject_region(polygon, safe, additional)
            return checkresult, (additional, safe)
        elif checkresult == RegionCheckResult.Refined:
            # We refined the existing region.
            # additional should contain the candidate for the counterexample.
            # compute setminus operation to get accepted constraints:
            # accepted = polygon.setminus(additional)

            # return checkresult, (accepted, safe)
            # TODO implement something.
            pass

        else:
            result_update = self.fail_region(polygon, safe)
            return checkresult, result_update
