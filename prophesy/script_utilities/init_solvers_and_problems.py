import logging

from prophesy.regions.region_solutionfunctionchecker import SolutionFunctionRegionChecker
from prophesy.regions.region_etrchecker import EtrRegionChecker
from prophesy.regions.region_plachecker import PlaRegionChecker
from prophesy.regions.region_checker import ProblemDescription
from prophesy.optimisation.pla_region_optimiser import PlaRegionOptimiser
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.input.modelfile import open_model_file
from prophesy.input.pctlfile import PctlFile
from prophesy.input.samplefile import read_samples_file
from prophesy.data.constant import parse_constants_string, Constants

from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.config import configuration
from prophesy.data.samples import InstantiationResultDict

logger = logging.getLogger(__name__)

def init_solvers_and_problem(cmdargs, optimisation = False):
    solvers = configuration.getAvailableSMTSolvers()
    ppmcs = configuration.getAvailableParametricMCs()
    configuration.check_tools()

    problem_description = ProblemDescription()
    constants = Constants()



    # TODO use better defaults for graph parameters
    if cmdargs.graph_preserving_pmc:
        problem_description.parameters.make_intervals_open()
    elif cmdargs.epsilon_pmc:
        # First, create the open interval
        problem_description.parameters.make_intervals_open()
        problem_description.parameters.make_intervals_closed(cmdargs.epsilon_pmc)


    if cmdargs.samples_file:
        logger.debug("Loading samples")
        sample_parameters, samples_threshold, samples = read_samples_file(cmdargs.samples_file,
                                                                          problem_description.parameters)
        if problem_description.parameters != sample_parameters:
            # TODO
            raise RuntimeError("Sampling and problem parameters are not equal")
    else:
        samples = InstantiationResultDict(parameters=problem_description.parameters)

    # TODO allow setting threshold via property:
    if not optimisation and cmdargs.threshold:
        problem_description.threshold = cmdargs.threshold
    logger.debug("Threshold: {}".format(problem_description.threshold))

    logger.debug("Setup Region Checker Interface")

    solver = None
    if cmdargs.z3:
        if 'z3' not in solvers:
            raise RuntimeError("Z3 location not configured.")
        solver = Z3CliSolver()
        solver.run()
    elif cmdargs.yices:
        if 'yices' not in solvers:
            raise RuntimeError("Yices location not configured.")
        solver = YicesCLISolver()
        solver.run()
    elif cmdargs.isat:
        if 'isat' not in solvers:
            raise RuntimeError("ISat location not configured.")
        solver = IsatSolver()
        solver.run()

    mc = None
    if cmdargs.storm:
        if 'storm-pars' not in ppmcs:
            raise RuntimeError("Storm location not configured.")
        mc = StormModelChecker()
    elif cmdargs.stormpy:
        if 'stormpy' not in ppmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        # Do not import at top, as stormpy might not be available.
        from prophesy.modelcheckers.stormpy import StormpyModelChecker

        mc = StormpyModelChecker()

    if cmdargs.etr:
        if solver is None:
            raise RuntimeError("For ETR an SMT solver is required.")
        checker = EtrRegionChecker(solver)
    elif cmdargs.sfsmt:
        if solver is None:
            raise RuntimeError("For using the solution function an SMT solver is required.")
        checker = SolutionFunctionRegionChecker(solver)
    elif cmdargs.pla and not optimisation:
        if mc is None:
            raise RuntimeError("For PLA, a model checker is required.")
        checker = PlaRegionChecker(mc)
    elif cmdargs.pla and optimisation:
        if mc is None:
            raise RuntimeError("For PLA, a model checker is required.")
        checker = PlaRegionOptimiser(mc)
    else:
        raise RuntimeError("No method for region checking selected.")

    logger.info("Generating regions")
    checker.initialize(problem_description, constants, fixed_threshold=not optimisation)
    if problem_description.welldefined_constraints is None:
        if mc is None:
            raise RuntimeError("If welldefinedness constraints are unknown, a model checker is required.")
        # TODO ugly, as the model checker needs to be initialized. Please refactor.
        # initialize model checker
        mc.load_model(problem_description.model, constants)
        mc.set_pctl_formula(problem_description.property)
        # compute constraints
        wd, gp = mc.get_parameter_constraints()
        problem_description.welldefined_constraints = wd
        problem_description.graph_preserving_constraints = gp

    return problem_description, checker, samples, solver, mc