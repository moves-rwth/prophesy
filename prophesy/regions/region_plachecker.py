from prophesy.regions.region_checker import RegionChecker, RegionCheckResult


class PlaRegionChecker(RegionChecker):
    def __init__(self, backend, parameters):
        """
        :param backend: 
        :type backend: ParametricModelChecker
        :param parameters: 
        """
        self._checker = backend
        self._parameters = parameters
        self.threshold = None

    def initialize(self, problem_description, threshold, constants=None):
        if not problem_description.model:
            raise ValueError("PLA requires the model to be present")
        if not problem_description.property:
            raise ValueError("PLA requires the property to be present")
        self._checker.load_model_from_prismfile(problem_description.model, constants)
        self._checker.set_pctl_formula(problem_description.property)
        self.threshold = threshold

    def print_info(self):
        pass

    def analyse_region(self, hyperrectangle, safe):
        hyperrectangle = hyperrectangle.close()
        regions = self._checker.check_hyperrectangle(self._parameters, hyperrectangle, self.threshold, safe)
        if len(regions) > 1:
            raise NotImplementedError("Not yet implemented")
        if len(regions) == 0:
            raise ValueError("Expected a result of some form")

        (regions_result, region) = regions[0]
        if region != hyperrectangle:
            raise RuntimeError("Expected the single region to coincide with the considered region")

        if regions_result == RegionCheckResult.Satisfied:
            return RegionCheckResult.Satisfied, None
        elif regions_result == RegionCheckResult.unknown:
            return RegionCheckResult.unknown, None
        else:
            raise ValueError("Pla is not expected to result other kind of results")
