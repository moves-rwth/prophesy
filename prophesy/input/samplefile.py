from prophesy.data.samples import SampleDict, SAMPLE_ABOVE, SAMPLE_BELOW
from pycarl import Rational, Variable
from prophesy.data.point import Point

def read_samples_file(path):
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

        # Variable is by default constructed as REAL, which is good here
        parameters = list(map(Variable, parameter_names))

        #Ignore thresholds
        if lines[1].startswith("Threshold"):
            if len(lines[1].split()) != 2:
                raise IOError("Invalid input on line 2")
            threshold = Rational(lines[1].split()[1])
            start += 1

        samples = SampleDict(parameters)
        for i, line in enumerate(lines[start:]):
            items = line.split()
            if len(items) - 1 != len(parameter_names):
                raise RuntimeError("Invalid input on line " + str(i + start))
            if items[-1] == "below":
                value = SAMPLE_BELOW
            elif items[-1] == "above":
                value = SAMPLE_ABOVE
            else:
                #TODO: falling back to Python float parser, but a good Rational parser is better
                value = Rational(float(items[-1]))
            coords = map(float, items[:-1])
            samples[Point(*coords)] = value

    return parameters, threshold, samples


def write_samples_file(variables, samples_dict, path):
    with open(path, "w") as f:
        f.write(" ".join(map(str, variables)) + "\n")
        for k, v in samples_dict.items():
            f.write("\t".join([("%.4f" % c) for c in k]) + "\t\t" + "%.20f" % v + "\n")
