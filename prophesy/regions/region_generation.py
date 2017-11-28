import os
import shutil
import tempfile
import logging
import shapely.geometry
from abc import ABCMeta, abstractmethod

from prophesy.data.samples import InstantiationResultDict
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.output.plot import Plot
from prophesy.util import ensure_dir_exists
import prophesy.config

from prophesy.regions.welldefinedness import WelldefinednessResult

logger = logging.getLogger(__name__)


class RegionGenerator:
    """
    A generator for regions. 
    This class acts as an iterable that generates new regions (or counterexamples),
    until the search space is exhausted (which possibly never happens).
    """
    __metaclass__ = ABCMeta

    def __init__(self, samples, parameters, threshold, checker, wd_constraints, gp_constraints):
        """
        Constructor.
        :param samples: List of samples.
        :param parameters: Parameters of the model.
        :param threshold: Threshold.
        :param checker: Region checker.
        :param wd_constraints: Well-defined constraints.
        :param gp_constraints: Graph-preserving constraints.
        """
        self.safe_samples, self.bad_samples, self.illdefined_samples = samples.copy().split(threshold)
        self.parameters = parameters
        self.threshold = threshold

        self.max_area_sum = HyperRectangle(*self.parameters.get_parameter_bounds()).size()

        self.checker = checker

        # Stores all regions as triple ([constraint], polygon representation, bad/safe)
        self.all_polys = []
        self.safe_polys = []
        self.bad_polys = []
        self.illdefined_polys = []
        self.new_samples = {}
        self.wd_constraints = wd_constraints
        self.gp_constraints = gp_constraints

        # Options for plotting.
        self._plot_candidates = False
        self.plot = len(self.parameters) <= 2
        self.first_pdf = True
        ensure_dir_exists(prophesy.config.configuration.get_plots_dir())
        _, self.result_file = tempfile.mkstemp(suffix=".pdf", prefix="result_", dir=prophesy.config.configuration.get_plots_dir())

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
        Add PDF with name to result.pdf in tmp directory.
        """
        if not prophesy.config.modules.is_module_available("pypdf2"):
            logging.warning("Module 'PyPDF2' is not available. PDF export is not supported.")
            return

        # Load module as it is available
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

    @abstractmethod
    def plot_candidate(self):
        """
        Plot the current candidate.
        """
        raise NotImplementedError("Abstract parent method")

    def plot_results(self, *args, **kwargs):
        """
        Plot results.
        :param args: Arguments.
        :param kwargs: Arguments.
        """
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
        samples_green = [instantiation.get_point(self.parameters) for instantiation in self.safe_samples.keys()]
        samples_red = [instantiation.get_point(self.parameters) for instantiation in self.bad_samples.keys()]
        samples_black = [instantiation.get_point(self.parameters) for instantiation in self.illdefined_samples.keys()]

        _, result_tmp_file = tempfile.mkstemp(".pdf", dir=prophesy.config.configuration.get_plots_dir())
        Plot.plot_results(parameters=self.parameters,
                          samples_green=samples_green,
                          samples_red=samples_red,
                          samples_black=samples_black,
                          path_to_save=result_tmp_file,
                          *args, **kwargs)
        self._add_pdf(result_tmp_file)
        os.unlink(result_tmp_file)

    # def is_inside_polygon(self, point, polygon):
    #    # checks if the point lies inside the polygon
    #    return point.within(polygon) or point.touches(polygon)

    # def intersects(self, polygon1, polygon2):
    #    """checks if two polygons intersect, touching is okay"""
    #    # TODO first check bounding boxes?
    #    return polygon1.intersects(polygon2) and not polygon1.touches(polygon2)

    # @abstractmethod
    # def refine_with_intersections(self, polygon):
    #    """Compute the intersections of the polygon with the existing ones
    #    and refine it by getting the difference
    #    returns the refined polygon"""
    #    raise NotImplementedError("Abstract parent method")

    @staticmethod
    def _area(region):
        """
        Get area of given region.
        :param region: Region.
        :return: Area of region.
        """
        if isinstance(region, HyperRectangle):
            return region.size()
        assert False

    @abstractmethod
    def next_region(self):
        """
        Generate a new region.
        :return Tuple (new region, well-definedness, safe/unsafe) or None if no next region exists.
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def fail_region(self):
        """
        Called after a region could not be checked, usually due to memout or timeout.
        Updates the current set of regions.
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def reject_region(self, sample):
        """
        Called after a region is rejected (sample found).
        :param sample: Sample acting as a counterexample for the constraint.
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def ignore_region(self):
        """
        Called for a region which is overall ill-defined. Skip it.
        """
        raise NotImplementedError("Abstract parent method")

    @abstractmethod
    def accept_region(self):
        """
        Called after a region is accepted.
        """
        raise NotImplementedError("Abstract parent method")

    def generate_constraints(self, max_iter=-1, max_area=1, plot_every_n=1, plot_candidates=True):
        """
        Iteratively generate new regions, heuristically, attempting to find the largest safe or unsafe area.
        :param max_iter: Number of regions to generate/check at most (not counting SMT failures), -1 for unbounded
        :param max_area: Maximal area percentage that should be covered.
        :param plot_every_n: How often should the plot be appended to the PDF.
        :param plot_candidates: True, iff candidates should be plotted.
        :return Tuple (safe regions, unsafe regions, samples)
        """
        if max_iter == 0:
            return self.safe_polys, self.bad_polys, self.new_samples

        self._plot_candidates = plot_candidates

        for result in self:
            res_status, data = result
            if res_status == WelldefinednessResult.Illdefined:
                self.all_polys.append((data, WelldefinednessResult.Illdefined))
                self.illdefined_polys.append(data)
            elif res_status == RegionCheckResult.Satisfied:
                self.all_polys.append(data)
                poly, safe = data
                if safe:
                    self.safe_polys.append(poly)
                else:
                    self.bad_polys.append(poly)
            elif res_status == RegionCheckResult.CounterExample:
                # Needs further checks
                pass
            elif res_status == RegionCheckResult.Refined:
                raise NotImplementedError("We have to record the refinement.")
                # self.all_polys.append()
            elif res_status == RegionCheckResult.Unknown:
                # Needs further checks
                pass
            else:
                assert False  # All options should be covered by switching if/else

            # Check termination criteria
            area_sum = sum(RegionGenerator._area(poly) for poly, safe in self.all_polys)
            if area_sum > max_area * self.max_area_sum:
                break

            max_iter -= 1
            if max_iter == 0:
                break

            # Plot intermediate result
            if res_status != RegionCheckResult.Unknown and len(self.all_polys) % plot_every_n == 0:
                self.plot_results(display=False)

        # Plot the final outcome
        if self.plot:
            self.plot_results(display=False)
            logging.info("Generation complete, plot located at {0}".format(self.result_file))
        self.checker.print_info()

        return self.safe_polys, self.bad_polys, self.new_samples

    def _analyse_region(self, region, welldefined, safe):
        """
        Analyse the given region.
        :param region: Region.
        :param welldefined: Flag iff the region is welldefined.
        :param safe: Flag iff the region should be considered safe.
        :return: Tuple (RegionCheckResult, (region/counterexample, safe))
        """
        assert welldefined == WelldefinednessResult.Welldefined
        checkresult, additional = self.checker.analyse_region(region, safe)
        if checkresult == RegionCheckResult.Satisfied:
            # remove unnecessary samples which are covered already by regions
            # TODO region might contain this info, why not use that.
            self.safe_samples = InstantiationResultDict({k: v for k, v in self.safe_samples.items() if not region.contains(k.get_point(self.parameters))}, parameters=self.parameters)
            self.bad_samples = InstantiationResultDict({k: v for k, v in self.bad_samples.items() if not region.contains(k.get_point(self.parameters))}, parameters=self.parameters)

            # TODO make the code above work with the polygons, as below.
            # for instantiation, _ in self.samples:
            #        if shapely.geometry.Point(*pt).within(polygon):
            #            del self.samples[pt]

            # update everything
            self.accept_region()
            return checkresult, (region, safe)
        elif checkresult == RegionCheckResult.CounterExample:
            # add new point as counter example to existing regions
            if additional.result >= self.threshold:
                self.safe_samples[additional.instantiation] = additional.result
            else:
                self.bad_samples[additional.instantiation] = additional.result
            self.reject_region(additional)
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
            self.fail_region()
            return RegionCheckResult.Unknown, (region, safe)
