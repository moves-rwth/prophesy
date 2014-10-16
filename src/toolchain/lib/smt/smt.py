from abc import ABCMeta, abstractmethod

from enum import Enum

class Answer(Enum):
    sat = 0
    unsat = 1
    unknown = 2
    
class VariableDomain(Enum):
    Bool = 0
    Real = 1
    Int = 2
    


class SMTSolver():
    __metaclass__ = ABCMeta

    @abstractmethod
    def name(self): raise NotImplementedError

    @abstractmethod
    def version(self): raise NotImplementedError

    @abstractmethod
    def check(): raise NotImplementedError

    @abstractmethod
    def push(): raise NotImplementedError

    @abstractmethod
    def pop(): raise NotImplementedError

    @abstractmethod
    def add_variable(): raise NotImplementedError

    @abstractmethod
    def assert_constraint(c): raise NotImplementedError

    @abstractmethod
    def assert_guarded_constraint(c): raise NotImplementedError

    @abstractmethod
    def set_guard(g, v): raise NotImplementedError

    @abstractmethod
    def from_file(p): raise NotImplementedError

    @abstractmethod
    def to_file(p): raise NotImplementedError


        
        
        
        