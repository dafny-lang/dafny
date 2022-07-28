"""Runtime enabling Dafny language features."""
import builtins
from dataclasses import dataclass
from contextlib import contextmanager
from fractions import Fraction
from collections import Counter
from functools import reduce
from types import GeneratorType
from itertools import chain, combinations
import copy

class classproperty(property):
    def __get__(self, instance, owner):
        return classmethod(self.fget).__get__(None, owner)()

def print(value):
    if value is None:
        builtins.print("null", end="")
    elif isinstance(value, bool):
        builtins.print("true" if value else "false", end="")
    else:
        builtins.print(value, end="")

@dataclass
class Break(Exception):
    target: str

class TailCall(Exception):
    pass

@contextmanager
def label(name: str = None):
    try:
        yield
    except Break as g:
        if g.target != name:
            raise g
    except TailCall as g:
        if name is not None:
            raise g

def _break(name):
    raise Break(target=name)

def _tail_call():
    raise TailCall()

class Seq(tuple):
    def __init__(self, __iterable = None, isStr = False):
        if __iterable is None:
            __iterable = []
        self.isStr = isStr \
                     or isinstance(__iterable, str) \
                     or (isinstance(__iterable, Seq) and __iterable.isStr) \
                     or (not isinstance(__iterable, GeneratorType)
                         and all(isinstance(e, str) and len(e) == 1 for e in __iterable)
                         and len(__iterable) > 0)

    @property
    def Elements(self):
        return self

    @property
    def UniqueElements(self):
        return frozenset(self)

    def __str__(self) -> str:
        if self.isStr:
            return ''.join(self)
        return '[' + ', '.join(map(str, self)) + ']'

    def __add__(self, other):
        return Seq(super().__add__(other), isStr=self.isStr and other.isStr)

    def __getitem__(self, key):
        if isinstance(key, slice):
            indices = range(*key.indices(len(self)))
            return Seq((self[i] for i in indices), isStr=self.isStr)
        return super().__getitem__(key)

    def set(self, key, value):
        l = list(self)
        l[key] = value
        return Seq(l, isStr=self.isStr)

    def __hash__(self) -> int:
        return hash(tuple(self))

class Set(frozenset):
    @property
    def Elements(self):
        return self

    @property
    def AllSubsets(self):
        # https://docs.python.org/3/library/itertools.html#itertools-recipes
        s = list(self)
        return map(Set, chain.from_iterable(combinations(s, r) for r in range(len(s)+1)))

    def __str__(self) -> str:
        return '{' + ', '.join(map(str, self)) + '}'

    def union(self, other):
        return Set(super().union(self, other))

    def intersection(self, other):
        return Set(super().intersection(other))

    def ispropersubset(self, other):
        return self.issubset(other) and self != other

    def __or__(self, other):
        return self.union(other)

    def __sub__(self, other):
        return Set(super().__sub__(other))

class MultiSet(Counter):
    def __str__(self) -> str:
        return 'multiset{' + ', '.join(map(str, self.elements())) + '}'

    def __len__(self):
        return reduce(lambda acc, key: acc + self[key], self, 0)

    def union(self, other):
        return MultiSet(self + other)

    def __or__(self, other):
        return self.union(other)

    def intersection(self, other):
        return MultiSet(self & other)

    def __sub__(self, other):
        return MultiSet(super().__sub__(other))

    @property
    def keys(self):
        return Set(key for key in self if self[key] > 0)

    def isdisjoint(self, other):
        return frozenset(self.keys).isdisjoint(frozenset(other.keys))

    def issubset(self, other):
        return all(self[key] <= other[key] for key in frozenset(self).union(frozenset(other)))

    def ispropersubset(self, other):
        return self.issubset(other) and len(self) < len(other)

    def set(self, key, value):
        set = Counter(self)
        set[key] = value
        return MultiSet(set)

    def __hash__(self):
        return hash(frozenset(self.keys))

    def __eq__(self, other):
        return all(self[key] == other[key] for key in self.keys | other.keys)

    def __setattr__(self, key, value):
        raise TypeError("'Map' object is immutable")

    def __contains__(self, item):
        return self[item] > 0

class Map(dict):
    def __str__(self) -> str:
        return 'map[' + ', '.join(map(lambda i: f'{i[0]} := {i[1]}', self.items)) + ']'

    @property
    def Elements(self):
        return self

    @property
    def keys(self):
        return Set(super().keys())

    @property
    def values(self):
        return Set(super().values())

    @property
    def items(self):
        return Set(super().items())

    def set(self, key, value):
        map = dict(self)
        map[key] = value
        return Map(map)

    def __sub__(self, other):
        map = dict(self)
        for key in list(other):
            map.pop(key, None)
        return Map(map)

    def __or__(self, other):
        map = dict(self)
        for k, v in other.items:
            map[k] = v
        return Map(map)

    def __hash__(self):
        return hash(frozenset(self))

    def __setattr__(self, key, value):
        raise TypeError("'Map' object is immutable")

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

def newArray(initValue, *dims):
    b = initValue
    for i in reversed(list(dims)):
        b = [copy.deepcopy(b) for _ in range(i)]
    return b

@dataclass
class HaltException(Exception):
    message: str

def quantifier(vals, frall, pred):
    for u in vals:
        if pred(u) != frall:
            return not frall
    return frall

def AllChars():
    return (chr(i) for i in range(0x10000))

class defaults:
    bool = staticmethod(lambda: False)
    int = staticmethod(lambda: 0)
    real = staticmethod(BigRational)
    pointer = staticmethod(lambda: None)
    tuple = staticmethod(lambda *args: lambda: tuple(a() for a in args))
