import sys
import threading
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

# Module: ExternConcurrent


class Option:
    @classmethod
    def default(cls, ):
        return lambda: Option_None()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_None(self) -> bool:
        return isinstance(self, Option_None)
    @property
    def is_Some(self) -> bool:
        return isinstance(self, Option_Some)
    def UnwrapOr(self, default):
        source0_ = self
        if source0_.is_None:
            return default
        elif True:
            d_0___mcc_h0_ = source0_.value
            d_1_v_ = d_0___mcc_h0_
            return d_1_v_

    def IsFailure(self):
        return (self).is_None

    def PropagateFailure(self):
        return Option_None()

    def Extract(self):
        return (self).value


class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'ExternConcurrent.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'ExternConcurrent.Option.Some({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_Some) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class MutableMap:
    def __init__(self) -> None:
        self.map = dict()
        self.lock = Lock()

    def Keys(self):
        self.lock.Lock__()
        s = self.map.keys()
        self.lock.Unlock()
        return _dafny.Set(s)

    def HasKey(self, k):
        self.lock.Lock__()
        b = k in self.map
        self.lock.Unlock()
        return b

    def Values(self):
        self.lock.Lock__()
        s = self.map.values()
        self.lock.Unlock()
        return _dafny.Set(s)

    def Items(self):
        self.lock.Lock__()
        s = self.map.items()
        self.lock.Unlock()
        return _dafny.Set(s)

    def Put(self, k, v):
        self.lock.Lock__()
        self.map[k] = v
        self.lock.Unlock()

    def Get(self, k):
        self.lock.Lock__()
        try:
            v = self.map.get(k)
        except KeyError:
            self.lock.Unlock()
            return Option_None()
        self.lock.Unlock()
        return Option_Some(v)

    def Remove(self, k):
        self.lock.Lock__()
        self.map.pop(k, None)
        self.lock.Unlock()

    def Cardinality(self):
        self.lock.Lock__()
        l = len(self.map)
        self.lock.Unlock()
        return l


class AtomicBox:
    def __init__(self, t) -> None:
        self.boxed = t

    def Get(self):
        return self.boxed
        
    def Put(self, t):
        self.boxed = t

class Lock:
    def __init__(self) -> None:
        self.lock = threading.Lock()

    def Lock__(self):
        self.lock.acquire()

    def Unlock(self):
        self.lock.release()