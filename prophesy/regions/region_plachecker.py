import time
from prophesy.regions.region_checker import RegionChecker, RegionCheckResult
from prophesy.data.hyperrectangle import HyperRectangle


class PlaRegionChecker(RegionChecker):
    def __init__(self, backend):
        """
        Constructor.
        :param backend: 
        :type backend: ParametricModelChecker
        :param parameters: 
        """
        super().__init__()
        self._checker = backend
        self._parameters = None
        self.threshold = None

    def initialize(self, problem_description, constants=None):
        if not problem_description.model:
            raise ValueError("PLA requires the model to be present")
        if not problem_description.property:
            raise ValueError("PLA requires the property to be present")
        self._checker.load_model_from_prismfile(problem_description.model, constants)
        self._parameters = problem_description.parameters
        self._checker.set_pctl_formula(problem_description.property)
        self.threshold = problem_description.threshold

    def supports_only_closed_regions(self):
        return True

    def analyse_region(self, hyperrectangle, safe):
        assert hyperrectangle.is_closed()
        start = time.time()
        regions = self._checker.check_hyperrectangle(self._parameters, hyperrectangle, self.threshold, safe)
        duration = time.time() - start
        if len(regions) > 1:
            raise NotImplementedError("Not yet implemented")
        if len(regions) == 0:
            raise ValueError("Expected a result of some form")

        (regions_result, region) = regions[0]
        if region != hyperrectangle:
            raise RuntimeError("Expected the single region to coincide with the considered region")

        if isinstance(region, HyperRectangle):
            self.benchmark_output.append((regions_result, duration, region.size()))
        else:
            self.benchmark_output.append((regions_result, duration, region.area))

        if regions_result == RegionCheckResult.Satisfied:
            return RegionCheckResult.Satisfied, None
        elif regions_result == RegionCheckResult.Unknown:
            return RegionCheckResult.Unknown, None
        else:
            raise ValueError("Pla is not expected to result other kind of results")
