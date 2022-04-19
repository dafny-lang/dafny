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
    def keys(self):
        return Seq(dict.keys(self))

class BigOrdinal:
    @staticmethod
    def is_limit(ord):
        return ord == 0

    @staticmethod
    def is_succ(ord):
        return 0 < ord

    @staticmethod
    def offset(ord):
        return ord

    @staticmethod
    def is_nat(ord):
        # at run time, every ORDINAL is a natural number
        return True

class BigRational(Fraction):
    def __str__(self):
        if self.denominator == 1:
            return f"{self.numerator}.0"
        correction = self.divides_a_power_of_10(self.denominator)
        if correction is None:
            return f"({self.numerator}.0 / {self.denominator}.0)"
        compensation, shift = correction
        if self.numerator < 0:
            sign, digits = "-", str(-self.numerator*compensation)
        else:
            sign, digits = "", str(self.numerator*compensation)
        if shift < len(digits):
            n = len(digits) - shift
            return f"{sign}{digits[:n]}.{digits[n:]}"
        return f"{sign}0.{'0' * (shift - len(digits))}{digits}"

    @staticmethod
    def isolate_factor(f, x):
        y = 0
        while x > 1 and x % f == 0:
            y += 1
            x //= f
        return x, y

    @staticmethod
    def divides_a_power_of_10(x):
        rem, expA = BigRational.isolate_factor(10, x)
        if rem % 5 == 0 or rem % 2 == 0 or rem == 1:
            major, minor = (5, 2) if rem % 5 == 0 else (2, 5)
            rem, expB = BigRational.isolate_factor(major, rem)
            return (minor**expB, expA+expB) if rem == 1 else None
        return None

    def __add__(self, other):
        return BigRational(super().__add__(other))

    def __sub__(self, other):
        return BigRational(super().__sub__(other))

    def __mul__(self, other):
        return BigRational(super().__mul__(other))

    def __truediv__(self, other):
        return BigRational(super().__truediv__(other))

def plus_char(a, b):
    return chr(ord(a) + ord(b))

def minus_char(a, b):
    return chr(ord(a) - ord(b))

def euclidian_division(a, b):
    if 0 <= a:
        if 0 <= b:
            return a // b
        else:
            return -(a // (-b))
    else:
        if 0 <= b:
            return -((-a-1) // b) - 1
        else:
            return (-a-1) // (-b) + 1

def euclidian_modulus(a, b):
    bp = abs(b)
    if 0 <= a:
        return a % bp
    c = (-a) % bp
    return c if c == 0 else bp - c
