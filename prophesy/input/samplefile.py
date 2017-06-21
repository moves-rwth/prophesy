import logging

from prophesy.data.samples import InstantiationResultDict, InstantiationResult,  ParameterInstantiation
from prophesy.adapter.pycarl import Rational, Variable
from prophesy.data.point import Point

logger = logging.getLogger(__name__)


def read_samples_file(path, parameters):
    """
    Reads sample files.

    The first line specifies the parameters (with an optional "Result" for the last column).
    The second line optionally specifies a threshold. This is important if we have binary samples,
    (for which we do not know the value, but just whether it is above or below the threshold).
    The remaining lines give the parameter values and the value. This value is either a number or
    "above" or "below".

    :param path:
    :return:
    """
    threshold = None
    with open(path, 'r') as f:
        lines = [l.strip() for l in f.readlines()]
        if len(lines) <= 2:
            raise RuntimeError("Samples file is empty or malformed")

        # read first line with variable names
        parameter_names = lines[0].split()
        if parameter_names[-1] == "Result":
            parameter_names = parameter_names[:-1]
        start = 1

        if parameters is None:
            # Variable is by default constructed as REAL, which is good here
            parameters = list(map(Variable, parameter_names))
            assert False, "No longer supported"


        #Ignore thresholds
        if lines[1].startswith("Threshold"):
            if len(lines[1].split()) != 2:
                raise IOError("Invalid input on line 2")
            threshold = Rational(lines[1].split()[1])
            start += 1

        samples = InstantiationResultDict(parameters)
        for i, line in enumerate(lines[start:]):
            items = line.split()
            if len(items) - 1 != len(parameter_names):
                logger.error("Invalid input in %s on line %s: '%s'", path, str(i + start), line)
                continue
            if items[-1] == "below":
                #TODO
                raise NotImplementedError("Inexact sampling results are not yet supported in v2")
                #value = SAMPLE_BELOW
            elif items[-1] == "above":
                #TODO
                raise NotImplementedError("Inexact sampling results are not yet supported in v2")
            else:
                #TODO: falling back to Python float parser, but a good Rational parser is better
                value = Rational(items[-1])
            coords = map(Rational, items[:-1])
            samples.add_result(InstantiationResult(ParameterInstantiation.from_point(Point(*coords), parameters), value))

    logger.debug("Parameters: %s", str(parameters))
    return parameters, threshold, samples


def write_samples_file(parameters, samples, path):
    logger.info("Write samples to %s", path)
    vars = parameters.get_variables()
    with open(path, "w") as f:
        f.write(" ".join(map(str, vars)) + "\n")
        for res in samples.instantiation_results():
            f.write("\t".join([str(c) for c in  res.instantiation.get_point(parameters).coordinates]))
            f.write("\t\t" + str(res.result) + "\n")
