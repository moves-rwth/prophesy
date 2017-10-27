import logging
import prophesy.adapter.pycarl as pc
from prophesy.data.hyperrectangle import HyperRectangle

logger = logging.getLogger(__name__)


class PlaSearchOptimisation():
    def __init__(self, pla_region_optimiser, problem_description, use_counterexample = True):
        self.pla_region_optimiser = pla_region_optimiser
        self.problem_description = problem_description
        self.use_counterexample = use_counterexample

    def search(self, requested_gap = pc.Rational("0.05"), max_iterations = 10, dir="max", lower=pc.Rational(0), upper = pc.Rational(1)):
        regions = [HyperRectangle(*self.problem_description.parameters.get_parameter_bounds())]

        regions = [region.close() for region in regions]
        iterations = 0

        assert dir in ["min", "max"]
        logger.info("Interval [{},{}] (size: {}) ".format(realised, bound, bound-realised))
        activity = [1.0 for _ in self.problem_description.parameters]
        nr_regions = 1
        while requested_gap < abs(bound - realised) and max_iterations >= iterations:
            curr_refinement_index = min(range(len(activity)), key=activity.__getitem__)
            iterations = iterations + 1
            this_lvl_bound = pc.Rational(0) if dir == "max" else pc.inf
            next_lvl_regions = []
            for region in regions:
                result = self.pla_region_optimiser.bound_value_in_hyperrectangle(self.problem_description.parameters, region, dir == "max")
                this_lvl_bound = max(this_lvl_bound, result) if dir == "max" else min(this_lvl_bound, result)
                if dir == "max" and result > realised + requested_gap:
                    next_lvl_regions = next_lvl_regions + region.split_in_single_dimension(iterations % len(self.problem_description.parameters))
                if dir == "min" and result < realised - requested_gap:
                    next_lvl_regions = next_lvl_regions + region.split_in_single_dimension(iterations % len(self.problem_description.parameters))

            regions = [region.close() for region in next_lvl_regions]

            change = float(len(regions))/nr_regions
            if bound != pc.inf:
                change = change - (1 if dir == "max" else -1) * float((bound - this_lvl_bound))
            bound = min(this_lvl_bound, bound) if dir == "max" else max(this_lvl_bound, bound)
            nr_regions = len(regions)
            logger.info("Iteration: {}, index={}; Interval [{},{}] (size: {} ~= {}, Regions: {})  ".format(iterations, curr_refinement_index, min(realised,bound), max(realised, bound), abs(bound - realised), float(abs(bound-realised)), len(regions)))


            activity = [(act/1.5 + 1 if curr_refinement_index != ind else act/1.5 + change) for ind, act in enumerate(activity)]