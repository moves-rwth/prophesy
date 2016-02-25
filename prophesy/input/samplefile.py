from collections import OrderedDict

def read_samples_file(path):
    """
    Reads sample files.

    The first line specifies the parameters (with an optional "Result") for the last column.
    The second line optionally specifies a threshold. This is important if we have binary samples,
    (for which we do not know the value, but just whether it is above or below the threshold).
    The remaining lines give the parameter values and the value. This value is either a number or
    "above" or "below".

    :param path:
    :return:
    """
    parameters = []
    samples = {}
    threshold = None
    with open(path, 'r') as f:
        lines = [l.strip() for l in f.readlines()]
        if len(lines) > 2:
            parameters = lines[0].split()
            if parameters[-1] == "Result":
                #TODO we thus disallow parameters with the name Result (see restrictions.md)
                parameters = parameters[:-1]
            start = 1
            #Ignore thresholds
            if lines[1].startswith("Threshold"):
                if len(lines[1].split()) != 2:
                    raise IOError("Invalid input on line 2")
                threshold = float(lines[1].split()[1])
                start += 1
            for i, line in enumerate(lines[start:]):
                items = line.split()
                if len(items) - 1 != len(parameters):
                    raise RuntimeError("Invalid input on line " + str(i + start))
                if(items[-1] == "below" or items[-1] == "above"):
                    samples[tuple(map(float, items[:-1]))] = items[-1]
                else:
                    samples[tuple(map(float, items[:-1]))] = float(items[-1])
            samples = OrderedDict(samples.items())
    return parameters, threshold, samples


def write_samples_file(parameters, samples_dict, path):
    with open(path, "w") as f:
        f.write(" ".join(parameters) + "\n")
        for k, v in samples_dict.items():
            f.write("\t".join([("%.4f" % c) for c in k]) + "\t\t" + "%.4f" % v + "\n")
