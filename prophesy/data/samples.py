
def split_samples(samples, threshold):
    """returns (>=, <)"""
    above_threshold = dict([(k, v) for k, v in samples.items() if v >= threshold])
    below_threshold = dict([(k, v) for k, v in samples.items() if v < threshold])
    return above_threshold, below_threshold

def filter_samples(samples, threshold, distance):
    """Returns samples which are less than (or equal) `distance` away
       from the threshold"""
    return {pt: val for pt, val in samples.items() if abs(threshold - val) <= distance}



