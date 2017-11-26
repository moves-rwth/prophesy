from prophesy.data.parameter import Parameter
import prophesy.adapter.pycarl as pc
import pycarl
import  pickle
from prophesy.data.interval import Interval, string_to_interval

def test_contains():
    pycarl.clear_variable_pool()
    x = pc.Variable("x")
    p = Parameter(x,  string_to_interval("(0,1)", int))
    p_new = pickle.loads(pickle.dumps(p))
    assert p == p_new