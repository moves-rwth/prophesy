import logging
import prophesy.adapter.pycarl as pc
from prophesy.data.hyperrectangle import HyperRectangle

logger = logging.getLogger(__name__)


class PlaSearchOptimisation():
    def __init__(self, pla_region_optimiser, problem_description, use_counterexample = True):
        self.pla_region_optimiser = pla_region_optimiser
        self.problem_description = problem_description
        self.use_counterexample = use_counterexample


    def search(self, realised, bound = pc.Rational("0.05"), requested_gap= pc.Rational("0.05"), max_iterations = 1000, dir="max"):
        regions = [(HyperRectangle(*self.problem_description.parameters.get_parameter_bounds()), 0)]

        regions = [(region.close(), x) for (region, x) in regions]
        iterations = 0

        param_id_to_index = dict([[p.id, i] for i, p in enumerate(self.problem_description.parameters)])
        index_to_param_id = dict([[i, p.id] for i, p in enumerate(self.problem_description.parameters)])
        assert dir in ["min", "max"]
        logger.info("Interval [{},{}] (size: {}) ".format(realised, bound, bound-realised))
        activity = [1.0 for _ in self.problem_description.parameters]
        nr_regions = 1
        while requested_gap < abs(bound - realised) and max_iterations >= iterations:
            #curr_refinement_index = iterations % len(self.problem_description.parameters)#min(range(len(activity)), key=activity.__getitem__) #iterations % len(self.problem_description.parameters)
            #print(curr_refinement_index)
            iterations = iterations + 1
            this_lvl_bound = pc.Rational(0) if dir == "max" else pc.inf
            next_lvl_regions = []
            for (region, i) in regions:
                result, estimates = self.pla_region_optimiser.bound_value_in_hyperrectangle(self.problem_description.parameters, region, dir == "max", generate_split_estimates=True)
                #print(estimates)
                curr_refinement_index =iterations % len(self.problem_description.parameters)# max(estimates, key=lambda k: estimates[k])
                #print([p.id for p in self.problem_description.parameters])
                if iterations % 20 < 10 or estimates[index_to_param_id[curr_refinement_index]] == 0:
                    curr_refinement_index = param_id_to_index[max(estimates, key=lambda k: estimates[k])]
                #print(curr_refinement_index)
                #print(estimates)
                #print(curr_refinement_index)
                this_lvl_bound = max(this_lvl_bound, result) if dir == "max" else min(this_lvl_bound, result)
                if dir == "max" and result > realised + requested_gap:
                    next_lvl_regions = next_lvl_regions + [(region.close(), curr_refinement_index) for region in region.split_in_single_dimension(curr_refinement_index)]
                if dir == "min" and result < realised - requested_gap:
                    next_lvl_regions = next_lvl_regions + [(region.close(), curr_refinement_index) for region in region.split_in_single_dimension(curr_refinement_index)]

            regions = next_lvl_regions
            #print(regions)

            lower = realised if dir == "max" else bound
            upper = bound if dir == "max" else realised
            logger.info("Iteration: {}, index={}; Interval [{},{}] (size: {} ~= {}, Regions: {})  ".format(iterations, curr_refinement_index, lower, upper, upper-lower, float(upper-lower), len(regions)))
            if nr_regions == 0:
                return True

            change = float(len(regions)) / nr_regions
            nr_regions = len(regions)
            if bound != pc.inf:
                change = change - (1 if dir == "max" else -1) * float(abs(bound - this_lvl_bound))
            bound = min(this_lvl_bound, bound) if dir == "max" else max(this_lvl_bound, bound)


            #activity = [(act/1.5 + 1 if curr_refinement_index != ind else act/1.5 + change) for ind, act in enumerate(activity)]
            #print(activity)
        return False