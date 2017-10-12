class PlaRegionOptimiser():
    def __init__(self, backend):
        """
        Constructor.
        :param backend: 
        :type backend: ParametricModelChecker
        :param parameters: 
        """
        self._checker = backend
        self._parameters = None

    def initialize(self, problem_description, constants=None, fixed_threshold=False):
        assert not fixed_threshold
        if not problem_description.model:
            raise ValueError("PLA requires the model to be present")
        if not problem_description.property:
            raise ValueError("PLA requires the property to be present")
        self._checker.load_model(problem_description.model, constants)
        self._parameters = problem_description.parameters
        self._checker.set_pctl_formula(problem_description.property)

    def supports_only_closed_regions(self):
        return True

    def analyse_upper_bound(self, region):
        return self._checker.bound_value_in_hyperrectangle(self._parameters, region, False)