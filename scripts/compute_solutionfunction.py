#!/usr/bin/env python3
import click
import logging

from prophesy.data.constant import parse_constants_string
from prophesy.input.modelfile import open_model_file
from prophesy.input.pctlfile import PctlFile
from prophesy.input.problem_description import ProblemDescription
from prophesy.input.solutionfunctionfile import write_pstorm_result
from prophesy.modelcheckers.storm import StormModelChecker
from prophesy.modelcheckers.prism import PrismModelChecker
from prophesy.config import configuration
from prophesy.sampling.sampler_ratfunc import RatFuncSampling
from prophesy.sampling.sampling import uniform_samples, refine_samples
from prophesy.input.samplefile import write_samples_file, read_samples_file
from prophesy.input.solutionfunctionfile import read_pstorm_result
from prophesy.smt.isat import IsatSolver
from prophesy.smt.Z3cli_solver import Z3CliSolver
from prophesy.smt.YicesCli_solver import YicesCLISolver
from prophesy.regions.region_solutionfunctionchecker import SolutionFunctionRegionChecker
from prophesy.regions.region_etrchecker import EtrRegionChecker
from prophesy.regions.region_plachecker import PlaRegionChecker

from prophesy.regions.region_quads import HyperRectangleRegions
import prophesy.adapter.pycarl as pc


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

pass_state = click.make_pass_decorator(ConfigState, ensure=True)




@click.group(chain=True)
@select_mc
@select_solver
@pass_state
def parameter_synthesis(config):
    config.obj = ConfigState()
    config.mc = make_modelchecker(config.mc)
    config.solver = make_solver(config.solver)


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

@parameter_synthesis.command()
@click.argument('threshold', type=pc.Rational)
@pass_state
def set_threshold(state, threshold):
    state.problem_description.threshold = threshold



@parameter_synthesis.command()
@click.argument('solution-file')
@pass_state
def load_solution_function(state, solution_file):
    result = read_pstorm_result(solution_file)
    state.problem_description.parameters = result.parameters
    state.problem_description.solution_function = result.ratfunc
    state.problem_description.welldefined_constraints = result.welldefined_constraints
    state.problem_description.graph_preserving_constraints = result.graph_preservation_constraints

@parameter_synthesis.command()
@click.option('--export')
@pass_state
def compute_solution_function(state, export):
    logging.info("Compute the rational function using " + state.mc.name() + " " + state.mc.version())
    state.mc.load_model(state.problem_description.model, state.problem_description.constants)
    state.mc.set_pctl_formula(state.problem_description.property)
    result = state.mc.get_rational_function()
    state.problem_description.solution_function = result.ratfunc
    state.problem_description.welldefined_constraints = result.welldefined_constraints
    state.problem_description.graph_preserving_constraints = result.graph_preservation_constraints
    if export:
        write_pstorm_result(export, result)
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
@pass_state
def sample(state, export, method, plot, samplingnr, iterations):
    logging.info("Compute samples..")

    if method == "evaluation":
        sampling_interface = RatFuncSampling(state.problem_description.solution_function, state.problem_description.parameters)
    elif method == "modelchecking":
        sampling_interface = state.mc
        state.mc.load_model(state.problem_description.model, state.problem_description.constants)
        state.mc.set_pctl_formula(state.problem_description.property)
    else:
        if method != "auto":
            raise RuntimeError("Method is expected to be either 'evaluation', 'modelchecking' or 'auto'")
        if state.problem_description.solution_function:
            sampling_interface = RatFuncSampling(state.problem_description.solution_function,
                                                 state.problem_description.parameters)
        else:
            sampling_interface = state.mc
            state.mc.load_model(state.problem_description.model, state.problem_description.constants)
            state.mc.set_pctl_formula(state.problem_description.property)

    logging.debug("Performing uniform sampling ")
    initial_samples = uniform_samples(sampling_interface, state.problem_description.parameters, samplingnr)
    #logging.info("Performing uniform sampling: {} samples".format(len(initial_samples)))


    logging.debug("Performing refined sampling ")
    refined_samples = refine_samples(sampling_interface, state.problem_description.parameters, initial_samples, iterations,
                                     state.problem_description.threshold)

    if export:
        write_samples_file(state.problem_description.parameters, refined_samples, export)

    if plot:
        if len(result.parameters) <= 2:
            plot_path = plot_samples(refined_samples, result.parameters, cmdargs.safe_above_threshold, threshold)

            if interactive:
                open_file(plot_path)
        else:
            logging.info("Cannot plot, as dimension is too high!")


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

@parameter_synthesis.command()
@click.option("--plot-every-n")
@click.option("--plot-candidates")
@click.option("--flip-red-green")
@pass_state
def configure_plotting(state):
    raise RuntimeError("Not yet (reimplemented)")


@parameter_synthesis.command()
@click.argument("verification-method")
@click.argument("region-method")
@click.option("--iterations", default=100)
@click.option("--area", type=pc.Rational, default=1)
@click.option("--epsilon", type=pc.Rational)
#@click.option("--gp")
@pass_state
def parameter_space_partitioning(state, verification_method, region_method, iterations, area, epsilon):
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
                                       plot_candidates=False)


def make_modelchecker(mc):
   # configuration.check_tools()
    pmcs = configuration.getAvailableParametricMCs()
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
    solvers = configuration.getAvailableSMTSolvers()

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
    parameter_synthesis()
