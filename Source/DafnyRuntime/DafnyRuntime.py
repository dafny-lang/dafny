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
        if self.denominator == 1:
            return f"{self.numerator}.0"
        decimal, compensation, shift = self.devidesAPowerOf10(self.denominator)
        if not decimal:
            return f"{self.numerator}.0 / {self.denominator}.0"
        if self.numerator < 0:
            sign, digits = "-", str(-self.numerator*compensation)
        else:
            sign, digits = "", str(self.numerator*compensation)
        if shift < len(digits):
            n = len(digits) - shift
            return f"{sign}{digits[:n]}.{digits[n:]}"
        return f"{sign}0.{'0' * (shift - len(digits))}{digits}"

    @staticmethod
    def deleteFactor(f, x):
        y = 0
        while True:
            if x > 1 and x % f == 0:
                y += 1
                x //= f
            else:
                return x == 1, x, y

    @staticmethod
    def devidesAPowerOf10(x):
        c, rem, expA = BigRational.deleteFactor(10, x)
        if c:
            return True, 1, expA
        if rem % 5 == 0 or rem % 2 == 0:
            major, minor = (5, 2) if rem % 5 == 0 else (2, 5)
            c, rem, expB = BigRational.deleteFactor(major, rem)
            return c, minor**expB, expA+expB
        return False, -1, -1

def PlusChar(a, b):
    return chr(ord(a) + ord(b))

def MinusChar(a, b):
    return chr(ord(a) - ord(b))
