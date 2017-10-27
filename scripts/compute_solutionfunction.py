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
    logging.info("Compute the rational function using " + state.mc.name() + " " + state.mc.version())

    constants = parse_constants_string(constants)
    click.echo(constants)
    state.problem_description.model = open_model_file(model_file)
    pctl_file = PctlFile(property_file)
    state.problem_description.property = pctl_file.get(pctl_index)
    state.problem_description.constants = constants



@parameter_synthesis.command()
@click.option('--export')
@pass_state
def compute_solution_function(state, export):
    logging.info("Compute the rational function using " + state.mc.name() + " " + state.mc.version())
    state.mc.load_model(state.problem_description.model, state.problem_description.constants)
    state.mc.set_pctl_formula(state.problem_description.property)
    result = state.mc.get_rational_function()
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
