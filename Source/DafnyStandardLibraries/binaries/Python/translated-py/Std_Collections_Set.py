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
import Std_Collections_Array
import Std_Collections_Imap
import Std_Functions
import Std_Collections_Iset
import Std_Collections_Map

# Module: Std_Collections_Set

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ExtractFromSingleton(s):
        def iife4_(_let_dummy_0):
            d_99_x_: TypeVar('T__') = None
            with _dafny.label("_ASSIGN_SUCH_THAT_d_1"):
                assign_such_that_1_: TypeVar('T__')
                for assign_such_that_1_ in (s).Elements:
                    d_99_x_ = assign_such_that_1_
                    if (d_99_x_) in (s):
                        raise _dafny.Break("_ASSIGN_SUCH_THAT_d_1")
                raise Exception("assign-such-that search produced no value (line 7299)")
                pass
            return d_99_x_
        return iife4_(0)
        

    @staticmethod
    def Map(f, xs):
        def iife5_():
            coll4_ = _dafny.Set()
            compr_4_: TypeVar('X__')
            for compr_4_ in (xs).Elements:
                d_101_x_: TypeVar('X__') = compr_4_
                if (d_101_x_) in (xs):
                    coll4_ = coll4_.union(_dafny.Set([f(d_101_x_)]))
            return _dafny.Set(coll4_)
        d_100_ys_ = iife5_()

        return d_100_ys_

    @staticmethod
    def Filter(f, xs):
        def iife6_():
            coll5_ = _dafny.Set()
            compr_5_: TypeVar('X__')
            for compr_5_ in (xs).Elements:
                d_103_x_: TypeVar('X__') = compr_5_
                if ((d_103_x_) in (xs)) and (f(d_103_x_)):
                    coll5_ = coll5_.union(_dafny.Set([d_103_x_]))
            return _dafny.Set(coll5_)
        d_102_ys_ = iife6_()

        return d_102_ys_

    @staticmethod
    def SetRange(a, b):
        d_104___accumulator_ = _dafny.Set({})
        while True:
            with _dafny.label():
                if (a) == (b):
                    return (_dafny.Set({})) | (d_104___accumulator_)
                elif True:
                    d_104___accumulator_ = (d_104___accumulator_) | (_dafny.Set({a}))
                    in26_ = (a) + (1)
                    in27_ = b
                    a = in26_
                    b = in27_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SetRangeZeroBound(n):
        return default__.SetRange(0, n)

