import logging
import prophesy.adapter.pycarl as pc
from prophesy.regions.region_checker import RegionCheckResult


from prophesy.data.hyperrectangle import HyperRectangle

logger = logging.getLogger(__name__)

class PlaSearchOptimisation():
    def __init__(self, pla_region_optimiser, problem_description, use_counterexample = True):
        self.pla_region_optimiser = pla_region_optimiser
        self.problem_description = problem_description
        self.use_counterexample = use_counterexample

    def search(self, requested_gap = pc.Rational("0.05"), max_iterations = 10, lower=pc.Rational(0), upper = pc.Rational(1)):
        regions = [HyperRectangle(*self.problem_description.parameters.get_variable_bounds())]
        regions = [region.close() for region in regions]
        iterations = 0
        logger.info("Interval [{},{}] (size: {}) ".format(lower, upper, upper-lower))
        activity = [1.0 for i in self.problem_description.parameters]
        nr_regions = 1
        while requested_gap < upper - lower and max_iterations >= iterations:
            curr_refinement_index =  min(range(len(activity)), key=activity.__getitem__)
            iterations = iterations + 1
            this_lvl_upper = pc.Rational(0)
            next_lvl_regions = []
            for region in regions:
                result = self.pla_region_optimiser.bound_value_in_hyperrectangle(self.problem_description.parameters, region, False)
                if result > lower + requested_gap:
                    this_lvl_upper = max(this_lvl_upper, result)
                    next_lvl_regions = next_lvl_regions + region.split_in_single_dimension(iterations % len(self.problem_description.parameters))

            regions = [region.close() for region in next_lvl_regions]

            change = float(len(regions))/nr_regions
            if upper != pc.inf:
                change = change - float((upper - this_lvl_upper))
            upper = min(this_lvl_upper, upper)
            nr_regions = len(regions)
            logger.info("Iteration: {}, index={}; Interval [{},{}] (size: {} ~= {}, Regions: {})  ".format(iterations, curr_refinement_index, lower, upper, upper - lower, float(upper-lower), len(regions)))
            activity = [(act/1.5 + 1 if curr_refinement_index != ind else act/1.5 + change) for ind, act in enumerate(activity)]
            print(activity)


