class ProblemDescription:
    def __init__(self, solutionfunction=None, parameters=None, model=None, property=None, wd_constraints=None,
                 gp_constraints=None, threshold=None, samples=None):
        """
        Constructor.
        :param solutionfunction: Rational function representing reachability probability.
        :param parameters: Parameters occuring in model and solution function.
        :param model: Model.
        :param property: Property.
        :param wd_constraints: Constraints for well formedness.
        :param gp_constraints: Constraints for graph preservation.
        """
        self.solutionfunction = solutionfunction
        self.parameters = parameters
        self.model = model
        self.property = property
        self.welldefined_constraints = wd_constraints
        self.graph_preserving_constraints = gp_constraints
        self.samples = samples
        self.threshold = threshold