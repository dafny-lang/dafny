"""Runtime enabling Dafny language features."""
import builtins
from dataclasses import dataclass
from contextlib import contextmanager
from fractions import Fraction
from collections import Counter
from collections.abc import Iterable
from functools import reduce
from types import GeneratorType, FunctionType
from itertools import chain, combinations, count

class classproperty(property):
    def __get__(self, instance, owner):
        return classmethod(self.fget).__get__(None, owner)()

def print(value):
    builtins.print(value, end="")

# Dafny strings are currently sequences of UTF-16 code units.
# To make a best effort attempt at printing the right characters we attempt to decode,
# but have to allow for invalid sequences.
def string_from_utf_16(utf_16_code_units):
    return b''.join(ord(c).to_bytes(2, 'little') for c in utf_16_code_units).decode("utf-16-le", errors = 'replace')

def string_of(value) -> str:
    if hasattr(value, '__dafnystr__'):
        return value.__dafnystr__()
    elif value is None:
        return "null"
    elif isinstance(value, bool):
        return "true" if value else "false"
    elif isinstance(value, str):
        # This is only for Dafny char values.
        # Dafny strings are represented as Seq's of individual char values,
        # and Seq defines __dafnystr__.
        return string_from_utf_16(value)
    elif isinstance(value, tuple):
        return '(' + ', '.join(map(string_of, value)) + ')'
    elif isinstance(value, FunctionType):
        return "Function"
    else:
        return str(value)

@dataclass
class Break(Exception):
    target: str

@dataclass
class Continue(Exception):
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

@contextmanager
def c_label(name: str = None):
    try:
        yield
    except Continue as g:
        if g.target != name:
            raise g

class CodePoint(str):

    escapes = {
      '\n' : "\\n",
      '\r' : "\\r",
      '\t' : "\\t",
      '\0' : "\\0",
      '\'' : "\\'",
      '\"' : "\\\"",
      '\\' : "\\\\",
    }

    def __escaped__(self):
        return self.escapes.get(self, self)

    def __dafnystr__(self):
        return f"'{self.__escaped__()}'"

    def __add__(self, other):
        return CodePoint(plus_char(self, other))

    def __sub__(self, other):
        return CodePoint(minus_char(self, other))

class Seq(tuple):
    def __init__(self, __iterable = None, isStr = False):
        '''
        isStr defines whether this value should be tracked at runtime as a string (a.k.a. seq<char>)
        It accepts three different values:
         - True: this value is definitely a string, mark it as such
         - False: this value might be a string, apply heuristics to make a best guess
         - None: don't apply heuristics, don't mark it as a string

        None is used when --unicode-char is true, to ensure consistent printing of strings
        across backends without depending on any runtime tracking.
        See docs/Compilation/StringsAndChars.md.
        '''

        if __iterable is None:
            __iterable = []
        if isStr is None:
            self.isStr = None
        else:
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

    def VerbatimString(self, asliteral):
        if asliteral:
            return f"\"{''.join(map(lambda c: c.__escaped__(), self))}\""
        else:
            return ''.join(self)

    def __dafnystr__(self) -> str:
        if self.isStr:
            # This should never be true when using --unicode-char,
            # so it is safe to assume we are a sequence of UTF-16 code units.
            return string_from_utf_16(self)
        return '[' + ', '.join(map(string_of, self)) + ']'

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

    def __lt__(self, other):
        return len(self) < len(other) and self == other[:len(self)]

    def __le__(self, other):
        return len(self) <= len(other) and self == other[:len(self)]

# Convenience for translation when --unicode-char is enabled
def SeqWithoutIsStrInference(__iterable = None):
    return Seq(__iterable, isStr = None)

class Array:
    def __init__(self, initValue, *dims):
        def create_structure(initValue, *dims):
            return [initValue if len(dims) <= 1 else create_structure(initValue, *dims[1:]) for _ in range(dims[0])]
        self.dims = list(dims)
        self.arr = create_structure(initValue, *dims)

    def __dafnystr__(self) -> str:
        return f'array{self.dims}'

    def __str__(self):
        return self.__dafnystr__()

    def length(self, i):
        return self.dims[i] if i < len(self.dims) else None

    def __len__(self):
        return self.length(0)

    def __getitem__(self, key):
        if not isinstance(key, Iterable):
            return self.arr[key]
        arr = self.arr
        for i in key:
            arr = arr[i]
        return arr

    def __setitem__(self, key, value):
        if not isinstance(key, Iterable):
            self.arr[key] = value
            return
        arr = self.arr
        for i in range(len(key)-1):
            arr = arr[key[i]]
        arr[key[-1]] = value

class Set(frozenset):
    @property
    def Elements(self):
        return self

    @property
    def AllSubsets(self):
        # https://docs.python.org/3/library/itertools.html#itertools-recipes
        s = list(self)
        return map(Set, chain.from_iterable(combinations(s, r) for r in range(len(s)+1)))

    def __dafnystr__(self) -> str:
        return '{' + ', '.join(map(string_of, self)) + '}'

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
    def __dafnystr__(self) -> str:
        return 'multiset{' + ', '.join(map(string_of, self.elements())) + '}'

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

    @property
    def Elements(self):
        return self.elements()

    @property
    def UniqueElements(self):
        return self.keys

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

    def __ne__(self, other):
        return not (self == other)

    def __setattr__(self, key, value):
        raise TypeError("'Map' object is immutable")

    def __contains__(self, item):
        return self[item] > 0

class Map(dict):
    def __dafnystr__(self) -> str:
        return 'map[' + ', '.join(map(lambda i: f'{string_of(i[0])} := {string_of(i[1])}', self.items)) + ']'

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
    def __dafnystr__(self):
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

@dataclass
class HaltException(Exception):
    message: str

def quantifier(vals, frall, pred):
    for u in vals:
        if pred(u) != frall:
            return not frall
    return frall

def AllBooleans():
    return [False, True]

def AllChars():
    return (chr(i) for i in range(0x10000))

def AllUnicodeChars():
    return chain((CodePoint(chr(i)) for i in range(0xD800)), 
                 (CodePoint(chr(i)) for i in range(0xE000, 0x11_0000)))

def AllIntegers():
    return (i//2 if i % 2 == 0 else -i//2 for i in count(0))

def IntegerRange(lo, hi):
    if lo is None:
        return count(hi-1, -1)
    if hi is None:
        return count(lo)
    return range(lo, hi)

class Doubler:
    def __init__(self, start):
        self.start = start

    def __iter__(self):
        i = self.start
        while True:
            yield i
            i *= 2

class defaults:
    bool = staticmethod(lambda: False)
    char = staticmethod(lambda: 'D')
    codepoint = staticmethod(lambda: CodePoint(defaults.char()))
    int = staticmethod(lambda: 0)
    real = staticmethod(BigRational)
    pointer = staticmethod(lambda: None)
    tuple = staticmethod(lambda *args: lambda: tuple(a() for a in args))
