from collections import OrderedDict
from enum import Enum
import prophesy.adapter.pycarl as pc

from prophesy.data.point import Point


class InexactRelation(Enum):
    LESS = 0
    LEQ = 1
    GEQ = 2
    GREATER = 3


class InexactInstantiationResult:
    def __init__(self, rel, threshold):
        self.relation = rel
        self.threshold = threshold


class InstantiationResultFlag(Enum):
    NOT_WELLDEFINED = 0


class ParameterInstantiation(dict):
    """Simple dictionary mapping from a Parameter to pycarl.Rational.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def get_parameters(self):
        parameters = []
        for k in self.keys():
            parameters.append(k)
        return set(parameters)

    def __sub__(self, other):
        assert self.get_parameters() == other.get_parameters()
        return self.get_point(self.get_parameters()) - other.get_point(other.get_parameters())

    def numerical_distance(self, other):
        assert self.get_parameters() == other.get_parameters()
        return self.get_point(self.get_parameters()).numerical_distance(other.get_point(other.get_parameters()))

    def distance(self, other):
        """
        Distance between two instantiations over the same parameters (in the same order)
        
        :param other: 
        :return: The distance
        """
        assert self.get_parameters() == other.get_parameters()
        return self.get_point(self.get_parameters()).distance(other.get_point(self.get_parameters()))

    def get_point(self, parameters):
        """Return the Point corresponding to this sample, given variable
        ordering provided as argument
        :param parameters: Must correspond to parameters of this sample point.
        :type parameters: Iterable[Parameter]
        """
        return Point(*[self[par] for par in parameters])

    @classmethod
    def from_point(cls, pt, parameters):
        """Construct ParameterInstantiation from Point and ParameterOrder
        
        :param pt: Point of pycarl.Rational
        :param parameters: ParameterOrder
        """
        return cls({param: val for param, val in zip(parameters, pt)})

    def to_formula(self):
        """Given list of variables, compute constraints

        :param variables: Variables for each dimension
        :return: A formula specifying the points inside the hyperrectangle
        :rtype: pc.Constraint or pc.Formula
        """
        constraint = pc.Constraint(True)
        for par in self.get_parameters():
            constraint = constraint & pc.Constraint(pc.Polynomial(par.variable) - self[par], pc.Relation.EQ)
        return constraint

    def __hash__(self):
        hsh = 0
        for v in self.values():
            hsh ^= hash(v)
        return hsh

    def __str__(self):
        return "{" + ";".join([k.name + ":" + str(v) for k,v in self.items()]) + "}"


class InstantiationResult:
    """Class to represent a single sample. Maps a point (tuple of
    pycarl.Rational) to a value (pycarl.Rational).
    """

    def __init__(self, instantiation, result):
        """
        :param instantiation:
        :param result: 
        """
        assert isinstance(instantiation, ParameterInstantiation)
        self.instantiation = instantiation
        self.result = result

    @property
    def well_defined(self):
        return self.result != InstantiationResultFlag.NOT_WELLDEFINED

    def get_instantiation_point(self, parameters):
        """
        
        :param variable_order: 
        :return: 
        """
        return self.instantiation.get_point(parameters)

    def get_parameters(self):
        """
        
        :return: 
        """
        return self.instantiation.get_parameters()

    @classmethod
    def from_point(cls, pt, res, parameters):
        """
        
        :param pt: 
        :param res: 
        :param parameters: 
        :return: 
        """
        return cls(ParameterInstantiation.from_point(pt, parameters), res)

    def __str__(self):
        return str(self.instantiation) + ": " + str(self.result)


class InstantiationResultDict(dict):
    """Maintains a set of instantiations with their results."""

    def __init__(self, *args, parameters=None):
        existing_dict, key_val_pairs = self._split_args_into_dict_and_pairs(args)
        self.parameters = set(parameters) if parameters is not None else self._deduce_parameters_from_args(existing_dict, key_val_pairs)


        for k, _ in existing_dict.items():
            self._validate_key(k)

        for k, _ in key_val_pairs:
            self._validate_key(k)
        super().__init__(existing_dict, *key_val_pairs)


    @staticmethod
    def _split_args_into_dict_and_pairs(args):
        if len(args) and hasattr(args[0], 'keys'):
            # first argument is a dictionary/mapping,
            # remaining (if any) need to be key-value pairs
            existing_dict = args[0]
            key_val_pairs = args[1:]
        else:
            existing_dict = {}
            key_val_pairs = args
        return existing_dict, key_val_pairs

    @staticmethod
    def _deduce_parameters_from_args(existing_dict, key_val_pairs):
        if len(existing_dict):
            return set(next(iter(existing_dict.keys())).get_parameters())
        elif len(key_val_pairs):
            return set(key_val_pairs[0][0].get_parameters())
        else:
            # I guess this could be implemented
            return None

    def _validate_key(self, key):
        if self.parameters is None:
            self.parameters = set(key.get_parameters())

        if key.get_parameters() != self.parameters:
            raise ValueError("Parameter mismatch")

    def _parameters_check(self):
        """
        :return: True if all variables are indeed set variables
        """
        return all([not p.variable.is_no_variable for p in self.parameters])  # !!

    def split(self, threshold):
        """Split given samples into separated sample dictionaries, where the value
        is either >= or < threshold or ill-defined.
        """
        above_threshold = InstantiationResultDict(parameters=self.parameters)
        below_threshold = InstantiationResultDict(parameters=self.parameters)
        illdefined = InstantiationResultDict(parameters=self.parameters)
        for k, v in self.items():
            if v == InstantiationResultFlag.NOT_WELLDEFINED:
                illdefined[k] = v
            elif v >= threshold:
                above_threshold[k] = v
            else:
                below_threshold[k] = v
        return above_threshold, below_threshold, illdefined

    def copy(self):
        return InstantiationResultDict(self, parameters=self.parameters)

    def __setitem__(self, key, value, *args, **kwargs):
        self._validate_key(key)
        super().__setitem__(key, value, *args, **kwargs)

def weighed_interpolation(sample1, sample2, threshold, fudge=0.0):
    """Interpolates between sample sample1 and sample2 to
    result in a point estimated close to the given threshold (by linear
    interpolation). Fudge allows to offset this point slightly either
    positively or negatively.
    
    :param sample1: Sample
    :param sample2: Sample
    :param threshold: The value we are interested in 
    :type threshold: pycarl.Rational
    :param fudge: Fraction of distance betwen both samples to fudge
        around
    :type fudge: float
    :return: tuple of pycarl.Rational if interpolated point, or None if the
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

    return ParameterInstantiation.from_point((deltas * weight + sample1.instantiation.get_point(sample1.get_parameters()).to_float()).to_nice_rationals(), sample1.get_parameters())
