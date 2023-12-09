import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Std_Wrappers
import Std_BoundedInts
import Std_Base64
import Std_Relations
import Std_Math
import Std_Collections_Seq

# Module: Std_Collections_Array

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BinarySearch(a, key, less):
        r: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        d_92_lo_: int
        d_93_hi_: int
        rhs0_ = 0
        rhs1_ = (a).length(0)
        d_92_lo_ = rhs0_
        d_93_hi_ = rhs1_
        while (d_92_lo_) < (d_93_hi_):
            d_94_mid_: int
            d_94_mid_ = _dafny.euclidian_division((d_92_lo_) + (d_93_hi_), 2)
            if less(key, (a)[d_94_mid_]):
                d_93_hi_ = d_94_mid_
            elif less((a)[d_94_mid_], key):
                d_92_lo_ = (d_94_mid_) + (1)
            elif True:
                r = Std_Wrappers.Option_Some(d_94_mid_)
                return r
        r = Std_Wrappers.Option_None()
        return r
        return r

