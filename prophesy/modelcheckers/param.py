from prophesy.modelcheckers.ppmc import ParametricProbabilisticModelChecker


class ParamParametricModelChecker(ParametricProbabilisticModelChecker):
    """
    Class wrapping the param model checker CLI.
    """

    def __init__(self):
        """
        Constructor.
        """
        raise NotImplementedError("Param is currently not supported")

    def name(self):
        raise NotImplementedError("Param is currently not supported")

    def set_bisimulation_type(self, BisimulationType):
        raise NotImplementedError("Param is currently not supported")

    def load_model_from_prismfile(self, prismfile, constants):
        raise NotImplementedError("Param is currently not supported")

    def version(self):
        raise NotImplementedError("Param is currently not supported")

    def get_rational_function(self):
        raise NotImplementedError("Param is currently not supported")

    def set_pctl_formula(self, formula):
        raise NotImplementedError("Param is currently not supported")

    def perform_sampling(self, samplepoints):
        raise NotImplementedError("Param is currently not supported")

    def check_hyperrectangle(self, parameter_ranges, threshold, hypothesis):
        raise NotImplementedError("Param is currently not supported")
