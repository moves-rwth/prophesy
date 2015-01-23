class Range():
    def __init__(self, lower_bound, upper_bound, step_size):
        self.start = lower_bound
        self.stop = upper_bound
        self.step = step_size

    def values(self):
        value_list = []
        i = self.start
        while i <= self.stop:
            value_list.append(i)
            i = i + self.step
        return value_list

def create_range_from_interval(interval, nr_samples):
    """Given closed interval [l,h], generate nr_sample
    steps in this interval"""
    assert(nr_samples > 1)
    assert(interval[0] <= interval[1])
    return Range(interval[0], interval[1], (interval[1] - interval[0]) / (nr_samples - 1))

