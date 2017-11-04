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
from prophesy.input.samplefile import write_samples_file
from prophesy.input.solutionfunctionfile import read_pstorm_result
import prophesy.adapter.pycarl as pc

import compute_solutionfunction

def select_mc(f):
    def callback(ctx, param, value):
        state = ctx.ensure_object(ConfigState)
        state.mc = value
        return value
    return click.option("--mc", expose_value=False, type=click.Choice(["stormpy","storm","prism"]), default="stormpy", callback=callback)(f)


class ConfigState(object):
    def __init__(self):
        self.mc = None
        self.problem_description = ProblemDescription()

pass_state = click.make_pass_decorator(ConfigState, ensure=True)




@click.group(chain=True)
@select_mc
@pass_state
def parameter_synthesis(config):
    config.obj = ConfigState()
    config.mc = make_modelchecker(config.mc)


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
    state.problem_description.graph_preservation_constraints = result.graph_preservation_constraints

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
    state.problem_description.graph_preservation_constraints = result.graph_preservation_constraints
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


if __name__ == "__main__":
    parameter_synthesis()
