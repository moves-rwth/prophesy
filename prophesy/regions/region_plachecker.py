from prophesy.regions.region_checker import RegionChecker

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

    def initialize(self, info, threshold, constants=None):
        if not info.model:
            raise ValueError("PLA requires the model to be present")
        if not info.property:
            raise ValueError("PLA requires the property to be present")
        self._checker.load_model_from_prismfile(info.model, constants)
        self._checker.set_pctl_formula(info.property)
        self.threshold = threshold

    def analyse_region(self, hyperrectangle, safe):
        regions = self._checker.check_hyperrectangle(self._parameters, hyperrectangle, self.threshold, safe)
        if len(regions) > 1:
            pass
