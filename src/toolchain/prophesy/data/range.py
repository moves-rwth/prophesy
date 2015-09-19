from numpy import arange


class Range:
    def __init__(self, lower_bound, upper_bound, step_size):
        self.start = lower_bound
        self.stop = upper_bound
        self.step = step_size

    def values(self):
        return list(arange(self.start, self.stop, self.step)) + [self.stop]


def create_range_from_interval(interval, nr_samples):
    """Given closed interval [l,h], generate nr_sample
    steps in this interval"""
    assert nr_samples > 1
    assert interval[0] <= interval[1]
    return Range(interval[0], interval[1], (interval[1] - interval[0]) / (nr_samples - 1))

