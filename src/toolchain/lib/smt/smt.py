from abc import ABCMeta, abstractmethod
from enum import Enum

class Answer(Enum):
    sat = 0
    unsat = 1
    unknown = 2
    killed = 3
    memout = 4

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
    def check(self): raise NotImplementedError

    @abstractmethod
    def push(self): raise NotImplementedError

    @abstractmethod
    def pop(self): raise NotImplementedError

    @abstractmethod
    def add_variable(self): raise NotImplementedError

    @abstractmethod
    def assert_constraint(self, c): raise NotImplementedError

    @abstractmethod
    def assert_guarded_constraint(self, c): raise NotImplementedError

    @abstractmethod
    def set_guard(self, g, v): raise NotImplementedError

    @abstractmethod
    def from_file(self, p): raise NotImplementedError

    @abstractmethod
    def to_file(self, p): raise NotImplementedError

    def __enter__(self):
        self.push()
        return self

    def __exit__(self, type, value, tb):
        self.pop()
