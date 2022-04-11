"""Runtime enabling Dafny language features."""
import builtins
from dataclasses import dataclass
from contextlib import contextmanager
from fractions import Fraction

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

class BigOrdinal:
    @staticmethod
    def IsLimit(ord):
        return ord == 0

    @staticmethod
    def IsSucc(ord):
        return 0 < ord

    @staticmethod
    def Offset(ord):
        return ord

    @staticmethod
    def IsNat(ord):
        # at run time, every ORDINAL is a natural number
        return True

class BigRational(Fraction):
    def __str__(self):
        if (self.denominator == 1):
            return f"{self.numerator}.0"
        try:
            log10 = self.intLog10(self.denominator)
        except ValueError:
            return f"{self.numerator}.0 / {self.denominator}.0"
        if(self.numerator < 0):
            sign = "-"
            digits = str(-self.numerator)
        else:
            sign = ""
            digits = str(self.numerator)
        if log10 < len(digits):
            n = len(digits) - log10
            return f"{sign}{digits[:n]}.{digits[n:]}"
        else:
            return f"{sign}0.{'0' * (log10 - len(digits))}{digits}"

    @staticmethod
    def intLog10(i):
        log10 = 0
        if i == 0:
            raise ValueError("must be called with a power of 10")
        # invariant: x != 0 && x * 10^log10 == old(x)
        while True:
            if i == 1:
                return log10
            elif i % 10 == 0:
                log10 += 1
                i //= 10
            else:
                raise ValueError("must be called with a power of 10")

def PlusChar(a, b):
    return chr(ord(a) + ord(b))

def MinusChar(a, b):
    return chr(ord(a) - ord(b))