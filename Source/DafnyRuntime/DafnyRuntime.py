"""Runtime enabling Dafny language features."""
import builtins
from dataclasses import dataclass
from contextlib import contextmanager

class classproperty(property):
    def __get__(self, instance, owner):
        return classmethod(self.fget).__get__(None, owner)()

def print(value):
    if isinstance(value, bool):
        builtins.print("true" if value else "false", end="")
    else:
        builtins.print(value, end="")

@dataclass
class Break(Exception):
    target: str

@contextmanager
def label(name: str):
    try:
        yield
    except Break as g:
        if g.target != name:
            raise g

def _break(name):
    raise Break(target=name)

class Seq(list):
    @property
    def Elements(self):
        return self

class Set(set):
    @property
    def Elements(self):
        return self

    def union(self, other):
        return Set(set.union(self, other))

    def __or__(self, other):
        return Set(set.union(self, other))

class Map(dict):
    @property
    def Elements(self):
        return self

    @property
    def Keys(self):
        return Seq(self.keys())
