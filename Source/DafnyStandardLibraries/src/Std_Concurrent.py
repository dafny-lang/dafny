import threading
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import _dafny
import Std_Wrappers

# Module: Std_Concurrent

class MutableMap:
    def ctor__(self, bytesKeys):
        pass
        
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
        try:
            self.map[k] = v
        except Exception as e:
            self.lock.Unlock()
            raise e
        self.lock.Unlock()

    def Get(self, k):
        self.lock.Lock__()
        try:
            v = self.map[k]
        except KeyError:
            self.lock.Unlock()
            return Std_Wrappers.Option_None()
        except Exception as e:
            self.lock.Unlock()
            raise e
        self.lock.Unlock()
        return Std_Wrappers.Option_Some(v)

    def Remove(self, k):
        self.lock.Lock__()
        self.map.pop(k, None)
        self.lock.Unlock()

    def Size(self):
        self.lock.Lock__()
        l = len(self.map)
        self.lock.Unlock()
        return l


class AtomicBox:
    def __init__(self) -> None:
        pass
        
    def ctor__(self, t):
        self.boxed = t
        pass

    def Get(self):
        return self.boxed
        
    def Put(self, t):
        self.boxed = t

class Lock:
    def ctor__(self):
        pass
        
    def __init__(self) -> None:
        self.lock = threading.Lock()

    def Lock__(self):
        self.lock.acquire()

    def Unlock(self):
        self.lock.release()
