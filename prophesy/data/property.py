import prophesy.adapter.pycarl as pc
from enum import Enum

class OperatorType(Enum):
    """
    Are we interested in probability or in reward
    """
    probability = 0
    reward = 1

    def __str__(self):
        if self == OperatorType.probability:
            return "P"
        else:
            return "R"

class OperatorDirection(Enum):
    min = 0
    max = 1
    unspecified = 2

    def __str__(self):
        if self == OperatorDirection.min:
            return "min"
        elif self == OperatorDirection.max:
            return "max"
        else:
            return ""

class OperatorBound(object):
    """
    Defines the operator bound. Can be left open to describe an operator bound which asks for the precise value. 
    """

    def __init__(self, relation=pc.Relation.EQ, threshold=None):
        """
        :param relation: The relation with which the actual probability is compared
        :type relation: pycarl.Relation
        :param threshold: The threshold 
        :type threshold: Any number type or None.
        """
        if not threshold and relation != pc.Relation.EQ:
            raise ValueError("If no threshold is given, the relation has to be '='")
        self.relation = relation
        self.threshold = threshold

    def asks_for_exact_value(self):
        """
        True if the bound describes the question for a precise boundary. 
        :return: 
        """
        return self.threshold is None

    def __str__(self):
        if self.asks_for_exact_value():
            return "=?"
        return str(self.relation) + str(self.threshold)

    @classmethod
    def from_string(cls, input):
        """
        Parsing Prism-style operator bounds
        :param input: 
        :type input: str
        :return: the bound
        :rtype: OperatorBound
        """

        if input[:2] == "<=":
            relation = pc.Relation.LEQ
            input = input[2:]
        elif input[:2] == ">=":
            relation = pc.Relation.GEQ
            input = input[2:]
        elif input[:2] == "!=":
            relation = pc.Relation.NEQ
            input = input[2:]
        elif input[0] == "<":
            relation = pc.Relation.LESS
            input = input[1:]
        elif input[0] == ">":
            relation = pc.Relation.GREATER
            input = input[1:]
        elif input[0] == "=":
            relation = pc.Relation.EQ
            if input[1] == "?":
                return cls()
            input = input[2:]
        else:
            raise ValueError("Cannot parse {} as a bound.".format(input))
        threshold = pc.Rational(input)
        return cls(relation, threshold)

class Property:
    """
    
    """
    def __init__(self, operator_type, operator_direction, reward_name, bound, pathformula):
        """
        
        :param operator_type: 
        :type operator_type: OperatorType
        :param bound: 
        :type bound: OperatorBound
        :param pathformula: 
        """
        self.operator = operator_type
        self.operator_direction = operator_direction
        self.reward_name = reward_name
        self.bound = bound
        self.pathformula = pathformula

    @classmethod
    def from_string(cls, input_string):
        """
        Parses prism-style properties
        :param input_string: 
        :type input_string: str
        :return: 
        :rtype: Property
        """
        input_string = input_string.strip()
        if input_string[:4] == "Pmin":
            input_string = input_string[4:]
            operator_direction = OperatorDirection.min
            operator_type = OperatorType.probability
        elif input_string[:4] == "Pmax":
            input_string = input_string[4:]
            operator_direction = OperatorDirection.max
            operator_type = OperatorType.probability
        elif input_string[:1] == "P":
            input_string = input_string[1:]
            operator_direction = OperatorDirection.unspecified
            operator_type = OperatorType.probability
        elif input_string[:4] == "Rmin":
            input_string = input_string[4:]
            operator_direction = OperatorDirection.min
            operator_type = OperatorType.reward
        elif input_string[:4] == "Rmax":
            input_string = input_string[4:]
            operator_direction = OperatorDirection.max
            operator_type = OperatorType.reward
        elif input_string[:1] == "R":
            input_string = input_string[1:]
            operator_direction = OperatorDirection.unspecified
            operator_type = OperatorType.reward
        else:
            ValueError("Expect property {} to start with P/Pmin/Pmax/R/Rmin/Rmax".format(input_string))

        reward_name = None
        if operator_type == OperatorType.reward and input_string[0] == "{":
            reward_name = input_string.split('}', 1)[0]
            input_string = input_string.split('}', 1)[1]


        operator_bound = OperatorBound.from_string(input_string.split(" ", 1)[0])

        input_string = input_string.split(" ",1)[1].strip()

        return cls(operator_type, operator_direction, reward_name, operator_bound, input_string)

    def __str__(self):
        return str(self.operator) + (self.reward_name if self.reward_name else "") + str(self.operator_direction) + str(self.bound) + " " + self.pathformula


