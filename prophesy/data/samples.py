from collections import OrderedDict, Set
from prophesy.data.point import Point
from enum import Enum


class InexactRelation(Enum):
    LESS = 0
    LEQ = 1
    GEQ = 2
    GREATER = 3


class InexactInstantiationResult():
    def __init__(self,rel, threshold):
        self.relation = rel
        self.threshold = threshold


class ParameterInstantiation(OrderedDict):
    """Simple dictionary mapping from a Parameter to pycarl.Rational.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def get_parameters(self):
        parameters = []
        for k in self.keys():
            parameters.append(k)
        return parameters

    def __sub__(self, other):
        assert self.get_parameters() == other.get_parameters()
        return self.get_point(self.get_parameters()) - other.get_point(other.get_parameters())

    def numerical_distance(self, other):
        assert self.get_parameters() == other.get_parameters()
        return self.get_point(self.get_parameters()).numerical_distance(other.get_point(other.get_parameters()))


    def distance(self, other):
        assert self.get_parameters() == other.get_parameters()
        return self.get_point(self.get_parameters()).distance(other.get_point(self.get_parameters()))

    def get_point(self, parameters = None):
        """Return the Point corresponding to this sample, given variable
        ordering provided as argument
        @param variables VariableOrder. Must correspond to variables of this
            sample point.
        """
        if not parameters:
            parameters = self.get_parameters()
        return Point(*[self[var] for var in parameters])

    @classmethod
    def from_point(cls, pt, parameters):
        """Construnct SamplePoint from Point and ParameterOrder
        @param pt Point of pycarl.Rational
        @param parameters ParameterOrder
        """
        sp = cls()
        for (val, var) in zip(pt, parameters):
            sp[var] = val
        return sp

    def __hash__(self):
        hsh = 0
        for v in self.values():
            hsh ^= hash(v)
        return hsh

class ParameterInstantiations(list):
    def __init__(self, *args):
        super().__init__(*args)
        self.parameters = None

    @classmethod
    def from_points(cls, pts, parameters):
        res = cls([ParameterInstantiation.from_point(pt, parameters) for pt in pts])
        res.parameters = parameters
        return res


class InstantiationResult(object):
    """Class to represent a single sample. Maps a point (tuple of
    pycarl.Rational) to a value (pycarl.Rational).
    """

    def __init__(self, instantiation, result):
        """
        @param pt data.Point. Order has to follow the canonical model order
        @param val pycarl.Rational
        @param variables VariableOrder (Optional)
        """
        assert isinstance(instantiation, ParameterInstantiation)
        self.instantiation = instantiation
        self.result = result

    def get_instantiation_point(self, variable_order):
        return self.instantiation.get_point(variable_order)

    def get_parameters(self):
        return self.instantiation.get_parameters()




class InstantiationResultDict():
    """
    Maintains a set of instantiations with their results.
    """

    def __init__(self, parameters):
        """
        @param variables, VariableOrder
        """
        self._values = OrderedDict()
        self.parameters = parameters
        assert self._parameters_check()

    def has(self, instantiation):
        return instantiation in self._values

    def _parameters_check(self):
        """
        
        :return: True if all variables are indeed set variables
        """
        for p in self.parameters:
            if p.variable.is_no_variable:
                return False
        return True

    def __iter__(self):
        return iter(self._values.items())

    def update(self, other):
        for k,v in other:
            assert isinstance(k, ParameterInstantiation)
            assert k.get_parameters() == self.parameters
            self._values[k] = v

    def __len__(self):
        return len(self._values)

    def add_result(self, instantiation_result):
        """
        @param sample Sample
        """
        assert isinstance(instantiation_result, InstantiationResult)
        assert instantiation_result.instantiation.get_parameters() == self.parameters
        self._values[instantiation_result.instantiation] = instantiation_result.result

    def split(self, threshold):
        """Split given samples into separated sample dictionaries, where the value
        either >= or < threshold.
        @param samples SampleDict
        @param threshold pycarl.Rational
        @return (SampleDict >=, SampleDict <)
        """
        above_threshold = InstantiationResultDict(self.parameters)
        below_threshold = InstantiationResultDict(self.parameters)
        for k, v in self._values.items():
            if v >= threshold:
                above_threshold._values[k] = v
            else:
                below_threshold._values[k] = v
        return above_threshold, below_threshold

    def filter(self, filter_func):
        """Returns samples for which filter_func returns true.
        @param samples SampleDict
        @param filter_func callable to filter values, return True to keep sample
        """
        filtered = InstantiationResultDict(self.parameters)
        for k, v in self._values.items():
            if filter_func(v):
                filtered._values[k] = v
        return filtered

    def copy(self):
        copied = InstantiationResultDict(self.parameters)
        for k, v in self._values.items():
            copied._values[k] = v
        return copied

    def instantiation_results(self):
        """Returns Sample instances, as generator
        """
        for pt, val in self._values.items():
            assert pt.get_parameters() == self.parameters
            yield InstantiationResult(pt, val)

    def instantiations(self):
        return self._values.keys()

    def check(self):
        """
        Validity check
        :return: True if instantiations map exactly the parameters to values
        """
        pass


def weighed_interpolation(sample1, sample2, threshold, fudge=0.0):
    """Interpolates between sample sample1 and sample2 to
    result in a point estimated close to the given treshold (by linear
    interpolation). Fudge allows to offset this point slightly either
    positively or negatively.
    @param sample1 Sample
    @param sample2 Sample
    @param threshold pycarl.Rational
    @param fudge float Percentage of distance betwen both samples to fudge
        around
    @return tuple of pycarl.Rational if interpolated point, or None if the
        values are too close
    """
    # If point values are too close, do not interpolate
    distance = abs(float(sample1.result) - float(sample2.result))
    if 10000*distance < 1:
        return None

    weight = abs(float(threshold) - float(sample1.result)) / distance

    deltas = (sample2.instantiation - sample1.instantiation).to_float()

    magnitude = sample1.instantiation.numerical_distance(sample2.instantiation)
    offset = abs(fudge) / magnitude

    # Positive fudge moves towards larger value
    if (sample1.result > sample2.result) == (fudge > 0):
        offset *= -1

    weight += offset

    return ParameterInstantiation.from_point((deltas * weight + sample1.instantiation.get_point().to_float()).to_nice_rationals(), sample1.get_parameters())


