#!/usr/bin/env python3
import logging
import time

import click
import prophesy.adapter.pycarl as pc
import prophesy.config
from prophesy.data.constant import parse_constants_string
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.data.samples import InstantiationResultDict
from prophesy.input.modelfile import open_model_file
from prophesy.input.pctlfile import PctlFile
from prophesy.input.problem_description import ProblemDescription
from prophesy.input.samplefile import write_samples_file, read_samples_file
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.input.solutionfunctionfile import write_pstorm_result
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.optimisation.heuristic_search import ModelOptimizer
from prophesy.regions.region_checker import RegionCheckResult
from prophesy.regions.region_etrchecker import EtrRegionChecker
from prophesy.regions.region_plachecker import PlaRegionChecker
from prophesy.regions.region_quads import HyperRectangleRegions
from prophesy.regions.region_solutionfunctionchecker import SolutionFunctionRegionChecker
from prophesy.regions.welldefinedness import check_welldefinedness, is_welldefined
from prophesy.sampling.sampler_ratfunc import RatFuncSampling
from prophesy.sampling.sampling import uniform_samples, refine_samples
from prophesy.smt.YicesCli_solver import YicesCLISolver
from prophesy.smt.Z3cli_solver import Z3CliSolver
from prophesy.smt.isat import IsatSolver
from prophesy.optimisation.qcqp import QcqpModelRepair
from prophesy.modelcheckers.pmc import BisimulationType

def select_mc(f):
    def callback(ctx, param, value):
        state = ctx.ensure_object(ConfigState)
        state.mc = value
        return value
    return click.option("--mc", expose_value=False, type=click.Choice(["stormpy","storm","prism"]), default="stormpy", callback=callback)(f)

def select_solver(f):
    def callback(ctx, param, value):
        state = ctx.ensure_object(ConfigState)
        state.solver = value
        return value
    return click.option("--solver", expose_value=False, type=click.Choice(["z3","yices","isat"]), default="z3", callback=callback)(f)

class ConfigState(object):
    def __init__(self):
        self.mc = None
        self.solver = None
        self.problem_description = ProblemDescription()
        self.overall_start_time = None

pass_state = click.make_pass_decorator(ConfigState, ensure=True)


def ensure_model_set(mc, model, constants, property):
    mc.load_model(model, constants)
    mc.set_pctl_formula(property)


@click.group(chain=True)
@select_mc
@select_solver
@click.option("--log-smt-calls")
@click.option("--config")
@click.option("--logfile", default="prophesy.log")
@pass_state
def parameter_synthesis(state, log_smt_calls, config, logfile):
    logging.basicConfig(filename=logfile, format='%(levelname)s:%(message)s', level=logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    logging.getLogger().addHandler(ch)
    logging.debug("Loading configuration")
    state.obj = ConfigState()
    state.overall_start_time = time.time()
    if config:
        prophesy.config.load_configuration(config)
    else:
        prophesy.config.load_configuration()
    from prophesy.config import configuration
    logging.debug("Loaded configuration")
    if configuration is None:
        raise RuntimeError("Something went wrong during initialisation of the configuration")
    state.mc = make_modelchecker(state.mc)
    state.solver = make_solver(state.solver)
    state.log_smt_calls = log_smt_calls
    return state


@parameter_synthesis.command()
@click.argument('model-file')
@click.argument('property-file')
@click.option('--constants')
@click.option('--pctl-index', default=0)
@pass_state
def load_problem(state, model_file, property_file, constants, pctl_index):
    constants = parse_constants_string(constants)
    click.echo(constants)
    state.problem_description.model = open_model_file(model_file)
    pctl_file = PctlFile(property_file)
    state.problem_description.property = pctl_file.get(pctl_index)
    state.problem_description.constants = constants
    state.problem_description.parameters = state.problem_description.model.parameters

    if not state.problem_description.property.bound.asks_for_exact_value():
        raise NotImplementedError("Only properties asking for the probability/reward '=?' are currently supported")
    if state.problem_description.model.contains_nondeterministic_model():
        if state.problem_description.property.operator_direction == OperatorDirection.unspecified:
            raise ValueError("For non-deterministic models, the operator direction should be specified.")
    ensure_model_set(state.mc, state.problem_description.model, state.problem_description.constants, state.problem_description.property)
    return state


@parameter_synthesis.command()
@click.argument('threshold', type=pc.Rational)
@pass_state
def set_threshold(state, threshold):
    state.problem_description.threshold = threshold
    return state

@parameter_synthesis.command()
@click.argument('bisimulation-type', type=click.Choice("none, strong, weak"))
@pass_state
def set_bisimulation(state, bisimulation_type):
    if bisimulation_type == "strong":
        btype = BisimulationType.strong
    if bisimulation_type == "weak":
        btype = BisimulationType.weak
    if bisimulation_type == "none":
        btype = BisimulationType.none
    state.mc.set_bisimulation_type(btype)

@parameter_synthesis.command()
@click.argument('solution-file')
@pass_state
def load_solution_function(state, solution_file):
    result = read_pstorm_result(solution_file)
    state.problem_description.parameters = result.parameters
    state.problem_description.solution_function = result.ratfunc
    state.problem_description.welldefined_constraints = result.welldefined_constraints
    state.problem_description.graph_preserving_constraints = result.graph_preservation_constraints
    return state

@parameter_synthesis.command()
@click.option('--export')
@pass_state
def compute_solution_function(state, export):
    logging.info("Compute the rational function using " + state.mc.name() + " " + state.mc.version())
    state.mc.load_model(state.problem_description.model, state.problem_description.constants)
    state.mc.set_pctl_formula(state.problem_description.property)
    result = state.mc.get_rational_function()
    state.problem_description.solution_function = result.ratfunc
    state.problem_description.parameters.update_variables(result.ratfunc.gather_variables())

    state.problem_description.welldefined_constraints = result.welldefined_constraints
    state.problem_description.graph_preserving_constraints = result.graph_preservation_constraints
    if export:
        write_pstorm_result(export, result)
    return state
    #
    # problem_parameters = [p for p in model_file.parameters if p not in constants]
    # if problem_parameters != result.parameters:
    #     if len(problem_parameters) != len(result.parameters):
    #         raise ValueError(
    #             "Parameters in model '{}' and in result '{}' do not coincide.".format(model_file.parameters,
    #                                                                                   result.parameters))
    #     for p in problem_parameters:
    #         if p not in result.parameters:
    #             raise ValueError(
    #                 "Parameters in model '{}' and in result '{}' do not coincide.".format(prism_file.parameters,
    #                                                                                       result.parameters))
    #     result.parameters = model_file.parameters


@parameter_synthesis.command()
@click.option('--export')
@click.option('--method', default="auto")
@click.option('--plot')
@click.option('--samplingnr', type=int, help='number of samples per dimension', default=4)
@click.option('--iterations', type=int, help='number of sampling refinement iterations', default=0)
@click.option('--stats', help="file to write sample stats to")
@pass_state
def sample(state, export, method, plot, samplingnr, iterations, stats):
    logging.info("Compute samples..")

    if method == "evaluation":
        sampling_interface = RatFuncSampling(state.problem_description.solution_function, state.problem_description.parameters)
    elif method == "modelchecking":
        sampling_interface = state.mc


    else:
        if method != "auto":
            raise RuntimeError("Method is expected to be either 'evaluation', 'modelchecking' or 'auto'")
        if state.problem_description.solution_function:
            sampling_interface = RatFuncSampling(state.problem_description.solution_function,
                                                 state.problem_description.parameters)
        else:
            sampling_interface = state.mc

    logging.debug("Performing uniform sampling ")
    uniform_sampling_time = time.time()
    initial_samples = uniform_samples(sampling_interface, state.problem_description.parameters, samplingnr)
    #logging.info("Performing uniform sampling: {} samples".format(len(initial_samples)))
    uniform_sampling_time = time.time() - uniform_sampling_time
    nr_initial_samples = len(initial_samples)
    nr_initial_samples_safe = len(initial_samples.split(state.problem_description.threshold)[0])

    logging.debug("Performing refined sampling ")
    refine_sampling_time = time.time()
    refined_samples = refine_samples(sampling_interface, state.problem_description.parameters, initial_samples, iterations,
                                     state.problem_description.threshold)
    refined_sampling_time = time.time() - refine_sampling_time

    if export:
        write_samples_file(state.problem_description.parameters, refined_samples, export)

    # Generate statistics
    stat_header = "\t".join(
        ["uniformsamples", "safesamplesinuniform", "ustime", "totalsamples", "safesamplesintotal", "refinetime"])
    stat_output = "{}\t\t{}\t\t\t{:.2f}\t{}\t\t{}\t\t\t{:.2f}".format(nr_initial_samples, nr_initial_samples_safe,
                                                          uniform_sampling_time, len(refined_samples), len(
            refined_samples.split(state.problem_description.threshold)[0]), refined_sampling_time)
    print(stat_header)
    print(stat_output)
    if stats:
        with open(stats, 'w') as file:
            file.write(stat_header + "\n")
            file.write(stat_output + "\n")

    if plot:
        if len(result.parameters) <= 2:
            plot_path = plot_samples(refined_samples, result.parameters, cmdargs.safe_above_threshold, threshold)

            if interactive:
                open_file(plot_path)
        else:
            logging.info("Cannot plot, as dimension is too high!")
    return state


@parameter_synthesis.command()
@click.argument('samples-file')
@pass_state
def load_samples(state, samples_file):
    sample_parameters, samples_threshold, samples = read_samples_file(samples_file,
                                                                      state.problem_description.parameters)
    if state.problem_description.parameters != sample_parameters:
        # TODO
        raise RuntimeError("Sampling and problem parameters are not equal")
    state.problem_description.samples = samples
    return state

@parameter_synthesis.command()
@click.option("--plot-every-n")
@click.option("--plot-candidates")
@click.option("--flip-red-green")
@pass_state
def configure_plotting(state):
    raise RuntimeError("Not yet (reimplemented)")


@parameter_synthesis.command()
@click.argument("dir", type=click.Choice(["min", "max"]))
@pass_state
def search_optimum(state, dir):
    if state.problem_description.solution_function:
        optimizer = ModelOptimizer(RatFuncSampling(state.problem_description.parameters, state.problem_description.parameters),
                                   state.problem_description.parameters, state.problem_description.property, dir)
        instance, val = optimizer.search()
        score = optimizer.score(None, val)
    else:
        #mc.set_welldefined_checker(SampleWelldefinedChecker(solver2, problem_description.parameters,problem_description.welldefined_constraints))
        optimizer = ModelOptimizer(state.mc, state.problem_description.parameters, state.problem_description.property, dir)
        instance, val = optimizer.search()
        score = optimizer.score(None, val)

    return state

@parameter_synthesis.command()
@click.option("--stats")
@click.option("--epsilon")
@click.argument("dir", type=click.Choice(["above", "below"]))
@click.argument("method")
@pass_state
def find_feasible_instantiation(state, stats, epsilon, dir, method):
    start_time = time.time()
    epsilon = 0.001
    if method in ["pso"]:
        # First, create the open interval
        state.problem_description.parameters.make_intervals_open()
        state.problem_description.parameters.make_intervals_closed(pc.Rational(epsilon))
    region = HyperRectangle(*state.problem_description.parameters.get_parameter_bounds())

    encoding_time = 0.0
    solver_time = 0.0
    iterations = 0



    if method in ["sfsmt", "etr"]:

        if method == "sfsmt":
            checker = SolutionFunctionRegionChecker(state.solver)
        elif method == "etr":
            checker = EtrRegionChecker(state.solver, state.mc)

        checker.initialize(state.problem_description, fixed_threshold=True)
        result, data = checker.analyse_region(region, dir == "below")
        encoding_time = checker.encoding_timer
        solver_time = checker.solver_timer

        if result == RegionCheckResult.Satisfied:
            print("No such point")
        elif result == RegionCheckResult.CounterExample:
            print("Point found: {}: {} (approx. {})".format(str(data.instantiation), str(data.result), float(data.result)))

    if method in ["qcqp"]:
        checker = QcqpModelRepair(state.mc)
        checker.initialize(state.problem_description, epsilon)
        result = checker.run(dir)
        encoding_time = checker.encoding_timer
        solver_time = checker.solver_time
        iterations = checker.iterations
        print("Point found: {}: {} (approx. {})".format(str(result.instantiation), str(result.result), float(result.result)))

    elif method in ["pso"]:
        start_wd_check = time.time()
        is_wd = is_welldefined(check_welldefinedness(state.solver, state.problem_description.parameters, region, state.mc.get_parameter_constraints()[1]))
        solver_time = time.time() - start_wd_check
        if not is_wd:
            raise NotImplementedError("PSO is currently assumes the full region is well-defined")
        optimizer = ModelOptimizer(state.mc, state.problem_description.parameters, state.problem_description.property,
                                   "max" if dir == "above" else "min", region=region)
        optimizer.set_termination_threshold(state.problem_description.threshold)
        result = optimizer.search()
        iterations = optimizer.iterations
        print("Point found: {}: {} (approx. {})".format(str(result.instantiation), str(result.result), float(result.result)))

    procedure_time = time.time() - start_time
    total_time = time.time() - state.overall_start_time

    print("This procedure took {}s (from start: {}s)".format(procedure_time, total_time))
    if stats:
        with open(stats, 'w') as file:
            file.write("total-time={}\n".format(total_time))
            file.write("procedure-time={}\n".format(procedure_time))
            file.write("encoding-time={}\n".format(encoding_time))
            file.write("solver-time={}\n".format(solver_time))
            file.write("mc-time={}\n".format(state.mc.instantiated_model_checking_time))
            file.write("iterations={}\n".format(iterations))
            file.write("model-building-time={}\n".format(state.mc.model_building_time))
            file.write("nr-mc-calls={}\n".format(state.mc.nr_samples_checked))

@parameter_synthesis.command()
@click.argument("destination")
@pass_state
def write_model_stats(state, destination):
    with open(destination, 'w') as file:
        file.write("states={}\n".format(state.mc.nr_states_before_bisim))
        file.write("transitions={}\n".format(state.mc.nr_transitions_before_bisim))
        file.write("nr-parameters={}\n".format(len(state.problem_description.parameters)))
        file.write("states-after-simplification={}\n".format(state.mc.nr_states))
        file.write("transitions-after-simplification={}\n".format(state.mc.nr_transitions))


# @parameter_synthesis.command()
# @click.argument("bound")
# @click.argument("verification-method")
# @pass_state
# def prove_bound(state, bound, verification_method):
#
#     if verification_method == "pla":
#         optimiser = PlaSearchOptimisation(state.mc, state.problem_description)
#
#     elif verification_method == "sfsmt":
#         pass #TODO use region checker for this.
#         raise NotImplementedError("Pretty straightforward application of a region checker.")
#     elif verification_method == "etr":
#         raise NotImplementedError("Pretty straightforward application of a region checker.")
#
#
#     if state.problem_description.property.operator_direction == OperatorDirection.max:
#         if state.problem_description.property.operator == OperatorType.reward:
#             bound = pc.inf
#         else:
#             bound = pc.Rational(1)
#     else:
#         bound = pc.Rational(0)
#     optimiser.search(requested_gap=cmdargs.gap, max_iterations=1, dir=optimal_dir, realised=state.problem,
#                      bound=bound)
#     return state
#
# @parameter_synthesis.command()
# @click.argument("verification-method")
# @pass_state
# def find_and_prove_bound(state, verification_method):
#     if verification_method == "pla":
#         raise RuntimeError("Currently, PLA can only be used to bound. We need to extend PlaSearchOptimisation")
#     elif verification_method == "etr":
#         optimiser = BinarySearchOptimisation(SolutionFunctionRegionChecker(state.solver), state.problem_description)
#     elif verification_method == "sfsmt":
#         optimiser = BinarySearchOptimisation(EtrRegionChecker(state.solver, state.mc), state.problem_description)
#
#
#     if state.problem_description.property.operator_direction == OperatorDirection.max:
#         if state.problem_description.property.operator == OperatorType.reward:
#             bound = pc.inf
#         else:
#             bound = pc.Rational(1)
#     else:
#         bound = pc.Rational(0)
#     optimiser.search(requested_gap=cmdargs.gap, max_iterations=cmdargs.iterations, dir=optimal_dir, realised=score,
#                      bound=bound)
#     return state


@parameter_synthesis.command()
@click.argument("verification-method")
@click.argument("region-method")
@click.option("--iterations", default=100)
@click.option("--area", type=pc.Rational, default=1)
@click.option("--epsilon", type=pc.Rational)
@click.option("--stats", help="File to write synthesis stats to")
#@click.option("--gp")
@pass_state
def parameter_space_partitioning(state, verification_method, region_method, iterations, area, epsilon, stats):
    if state.problem_description.samples is None:
        state.problem_description.samples = InstantiationResultDict(parameters=state.problem_description.parameters)

    if verification_method in ["etr", "pla"] or state.problem_description.welldefined_constraints is None:
        # TODO dont do this always (that is, if it has been loaded before..)
        state.mc.load_model(state.problem_description.model, state.problem_description.constants)
        state.mc.set_pctl_formula(state.problem_description.property)

    #TODO only do this when gp is set
    state.problem_description.parameters.make_intervals_open()

    if epsilon:
        # First, create the open interval
        state.problem_description.parameters.make_intervals_open()
        state.problem_description.parameters.make_intervals_closed(epsilon)


    if state.problem_description.welldefined_constraints is None:
        if state.mc is None:
            raise RuntimeError("If welldefinedness constraints are unknown, a model checker is required.")

        # initialize model checker
        # compute constraints
        wd, gp = state.mc.get_parameter_constraints()
        state.problem_description.welldefined_constraints = wd
        state.problem_description.graph_preserving_constraints = gp


    if verification_method == "etr":
        if state.solver is None:
            raise RuntimeError("For ETR an SMT solver is required.")
        if state.mc.name() != "stormpy":
            raise RuntimeError("For ETR stormpy is required.")
        checker = EtrRegionChecker(state.solver, state.mc)
    elif verification_method == "sfsmt":
        if state.solver is None:
            raise RuntimeError("For using the solution function an SMT solver is required.")
        checker = SolutionFunctionRegionChecker(state.solver)
    elif verification_method == "pla":
        if state.mc is None:
            raise RuntimeError("For PLA, a model checker is required.")
        checker = PlaRegionChecker(state.mc)
    else:
        raise RuntimeError("No method for region checking selected.")


    logging.info("Generating regions")
    checker.initialize(state.problem_description, fixed_threshold=True)

    generator = HyperRectangleRegions(state.problem_description.samples,
                                      state.problem_description.parameters,
                                      state.problem_description.threshold,
                                      checker,
                                      state.problem_description.welldefined_constraints,
                                      state.problem_description.graph_preserving_constraints,
                                      split_uniformly=region_method == "quads")

    generator.generate_constraints(max_iter=iterations, max_area=area, plot_every_n=100000,
                                       plot_candidates=False, export_statistics=stats)
    return state

def make_modelchecker(mc):
   # configuration.check_tools()
    pmcs = prophesy.config.configuration.getAvailableParametricMCs()
    if mc == "storm":
        if 'storm' not in pmcs:
            raise RuntimeError("Storm location not configured.")
        tool = StormModelChecker()
    elif mc == "prism":
        if 'prism' not in pmcs:
            raise RuntimeError("Prism location not configured.")
        tool = PrismModelChecker()
    elif mc == "stormpy":
        if 'stormpy' not in pmcs:
            raise RuntimeError("Stormpy dependency not configured.")
        from prophesy.modelcheckers.stormpy import StormpyModelChecker
        tool = StormpyModelChecker()
    else:
        raise RuntimeError("No supported model checker defined")
    return tool


def make_solver(solver):
    solvers = prophesy.config.configuration.getAvailableSMTSolvers()

    if solver == "z3":
        if 'z3' not in solvers:
            raise RuntimeError("Z3 location not configured.")
        tool = Z3CliSolver()
    elif solver == "yices":
        if 'yices' not in solvers:
            raise RuntimeError("Yices location not configured.")
        tool = YicesCLISolver()
    elif solver == "isat":
        if 'isat' not in solvers:
            raise RuntimeError("ISat location not configured.")
        tool = IsatSolver()
    tool.run()
    return tool

if __name__ == "__main__":
    state = parameter_synthesis.main(standalone_mode=False)[0]
    state.solver.stop()
    if state.log_smt_calls:
        state.solver.to_file(state.log_smt_calls)
    while len(logging.getLogger().handlers) > 0:
        h = logging.getLogger().handlers[0]
        logging.debug('Removing handler %s' % str(h))
        logging.getLogger().removeHandler(h)
        #logging.debug('%d more to go' % len(logging.getLogger().handlers))

