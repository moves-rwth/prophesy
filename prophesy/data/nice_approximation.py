from prophesy.adapter.pycarl import Rational, Integer


class FixedDenomFloatApproximation:
    def __init__(self, denom):
        self.denom = Integer(denom)

    def find(self, input):
        return Rational(Integer(int(float(input)*float(self.denom))), self.denom)
