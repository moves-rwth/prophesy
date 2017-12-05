import os
import shutil
import tempfile
import logging
import time
from abc import ABCMeta, abstractmethod

from prophesy.data.samples import InstantiationResultDict
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.output.plot import Plot
from prophesy.util import ensure_dir_exists
import prophesy.config

from prophesy.regions.welldefinedness import WelldefinednessResult

logger = logging.getLogger(__name__)


class GenerationRecord:
    def __init__(self):
        self._region = None
        self._result = None
        self._analysis_time = None
        self._search_time = None
        self._iteration_time = None
        self._safe = None

    def set_region(self, region, safe):
        self._region = region
        self._safe = safe

    def set_result(self, result):
        self._result = result

    def start_analysis_timer(self):
        assert self._analysis_time is None
        self._analysis_time = time.time()

    def start_generation_timer(self):
        assert self._search_time is None
        self._search_time = time.time()

    def start_iteration_timer(self):
        assert self._iteration_time is None
        self._iteration_time = time.time()

    def stop_analysis_timer(self):
        assert self._analysis_time is not None
        self._analysis_time = time.time() - self._analysis_time

    def stop_generation_timer(self):
        assert self._search_time is not None
        self._search_time = time.time() - self._search_time

    def stop_iteration_timer(self):
        assert self._iteration_time is not None
        self._iteration_time = time.time() - self._iteration_time

    @property
    def region(self):
        return self._region

    @property
    def covered_area(self):
        if self._result in [WelldefinednessResult.Illdefined, RegionCheckResult.Satisfied]:
            return self._region.size()
        else:
            return 0.0

    @property
    def result(self):
        return self._result

    @property
    def analysis_time(self):
        return self._analysis_time

    @property
    def generation_time(self):
        return self._search_time

    @property
    def iteration_time(self):
        return self._iteration_time

    @property
    def safe(self):
        return self._safe

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

        self._records = []
        self._iteration_timer = None

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
        self.start_iteration()
        self.start_generation()
        region_info = self.next_region()
        self.stop_generation()
        while region_info is not None:
            polygon, welldefined, area_safe = region_info
            if self._plot_candidates:
                self.plot_candidate()
            self.start_analysis()
            res =  self._analyse_region(polygon, welldefined, area_safe)
            self.stop_analysis()
            self.stop_iteration()
            yield res
            self.start_iteration()
            # get next constraint depending on algorithm
            self.start_generation()
            region_info = self.next_region()
            self.stop_generation()

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

    def record_accepted(self, region, safe):
        """
        Record the accepted region.
        
        :return: 
        """
        logger.info("Region accepted")

        self.all_polys.append((region, RegionCheckResult.Satisfied))
        if safe:
            self.safe_polys.append(region)
        else:
            self.bad_polys.append(region)
        self._records[-1].set_region(region, safe)
        self._records[-1].set_result(RegionCheckResult.Satisfied)

    def record_cex(self, region, safe, additional):
        """
        :param additional: An additional sample.
        :return: 
        """
        logger.info("Counterexample found")
        if additional.result >= self.threshold:
            self.safe_samples[additional.instantiation] = additional.result
        else:
            self.bad_samples[additional.instantiation] = additional.result

        self._records[-1].set_region(region, safe)
        self._records[-1].set_result(RegionCheckResult.Unknown)

    def record_unknown(self, region, safe):
        logger.info("No result found")
        self._records[-1].set_region(region, safe)
        self._records[-1].set_result(RegionCheckResult.Unknown)

    def record_illdefined(self, region):
        logger.info("Region is illdefined")
        self.all_polys.append((region, WelldefinednessResult.Illdefined))
        self.illdefined_polys.append(region)

        self._records[-1].set_result(WelldefinednessResult.Illdefined)

    def start_iteration(self):
        logger.info("Start next iteration")

        self._records.append(GenerationRecord())
        self._records[-1].start_iteration_timer()

    def start_analysis(self):
        print("start analysis timer")
        self._records[-1].start_analysis_timer()

    def stop_analysis(self):
        print("stop analysis timer")
        self._records[-1].stop_analysis_timer()
        print(self._records[-1].analysis_time)

    def start_generation(self):
        self._records[-1].start_generation_timer()

    def stop_generation(self):
        self._records[-1].stop_generation_timer()

    def stop_iteration(self):
        self._records[-1].stop_iteration_timer()
        print(self._records[-1].iteration_time)
        logger.info("Done with iteration: took %s", str(self._records[-1].iteration_time))


    def generate_constraints(self, max_iter=-1, max_area=1, plot_every_n=1, plot_candidates=True, export_statistics = None):
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

        for result, additional_info in self:

            if export_statistics:
                self.export_stats(export_statistics, update=True)
            # Check termination criteria
            area_sum = sum(poly.size() for poly, safe in self.all_polys)
            if area_sum > max_area * self.max_area_sum:
                break

            max_iter -= 1
            if max_iter == 0:
                break

            # Plot intermediate result
            if result != RegionCheckResult.Unknown: #and len(self.all_polys) % plot_every_n == 0:
                self.plot_results(display=True)


        # Plot the final outcome
        if self.plot:
            self.plot_results(display=False)
            logging.info("Generation complete, plot located at {0}".format(self.result_file))




        return self.safe_polys, self.bad_polys, self.new_samples

    def export_stats(self, filename, update=False):
        logging.debug("Write stats to %s (update == %s)", filename, str(update))
        with open(filename, 'a') as file:
            if not update or len(self._records) == 1:
                file.write("\t".join(["N", "cons. area", "res", "safe", "gentime", "anatime", "ttime", "cov. area", "cumgentime", "cumanatime", "cumttime"]))
                file.write("\n")
            cov_area = 0.0
            cumulative_generation_time = 0.0
            cumulative_analysis_time = 0.0
            cumulative_total_time = 0.0
            for idx, r in enumerate(self._records):
                cov_area += float(r.covered_area)
                cumulative_generation_time += r.generation_time
                cumulative_analysis_time += r.analysis_time
                cumulative_total_time += r.iteration_time
                if not update or len(self._records) == idx + 1:
                    file.write("\t".join([str(x) for x in [idx, r.region.size(), r.result, r.safe, r.generation_time, r.analysis_time, r.iteration_time, cov_area, cumulative_generation_time, cumulative_analysis_time, cumulative_total_time]]))
                    file.write("\n")


    def _analyse_region(self, region, welldefined, safe):
        """
        Analyse the given region.
        :param region: Region.
        :param welldefined: Flag iff the region is welldefined.
        :param safe: Flag iff the region should be considered safe.
        :return: Tuple (RegionCheckResult, (region/counterexample, safe))
        """
        print(region)
        if welldefined == WelldefinednessResult.Illdefined:
            self.ignore_region()
            self.record_illdefined(region)
            return WelldefinednessResult.Illdefined, region

        assert welldefined == WelldefinednessResult.Welldefined
        checkresult, additional = self.checker.analyse_region(region, safe)
        if checkresult == RegionCheckResult.Satisfied:
            # remove unnecessary samples which are covered already by regions
            # TODO region might contain this info, why not use that.
            self.safe_samples = InstantiationResultDict({k: v for k, v in self.safe_samples.items() if not region.contains(k.get_point(self.parameters))}, parameters=self.parameters)
            self.bad_samples = InstantiationResultDict({k: v for k, v in self.bad_samples.items() if not region.contains(k.get_point(self.parameters))}, parameters=self.parameters)

            # update everything
            self.accept_region()
            self.record_accepted(region, safe)
            return checkresult, (region, safe)
        elif checkresult == RegionCheckResult.CounterExample:
            # add new point as counter example to existing regions

            self.reject_region(additional)
            self.record_cex(region, safe, additional)
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
            self.record_unknown(region, safe)
            return RegionCheckResult.Unknown, (region, safe)






