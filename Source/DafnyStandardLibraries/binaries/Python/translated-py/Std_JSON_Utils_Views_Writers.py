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
import Std_Collections_Set
import Std_Collections
import Std_DynamicArray
import Std_FileIO
import Std_Arithmetic_GeneralInternals
import Std_Arithmetic_MulInternalsNonlinear
import Std_Arithmetic_MulInternals
import Std_Arithmetic_Mul
import Std_Arithmetic_ModInternalsNonlinear
import Std_Arithmetic_DivInternalsNonlinear
import Std_Arithmetic_ModInternals
import Std_Arithmetic_DivInternals
import Std_Arithmetic_DivMod
import Std_Arithmetic_Power
import Std_Arithmetic_Logarithm
import Std_Arithmetic_Power2
import Std_Arithmetic
import Std_Strings_HexConversion
import Std_Strings_DecimalConversion
import Std_Strings_CharStrEscaping
import Std_Strings
import Std_Unicode_Base
import Std_Unicode_Utf8EncodingForm
import Std_Unicode_Utf16EncodingForm
import Std_Unicode_UnicodeStringsWithUnicodeChar
import Std_Unicode_Utf8EncodingScheme
import Std_Unicode
import Std_PythonConcurrent
import Std_PythonFileIOInternalExterns
import Std_JSON_Values
import Std_JSON_Errors
import Std_JSON_Spec
import Std_JSON_Utils_Views_Core

# Module: Std_JSON_Utils_Views_Writers


class Chain:
    @classmethod
    def default(cls, ):
        return lambda: Chain_Empty()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Empty(self) -> bool:
        return isinstance(self, Chain_Empty)
    @property
    def is_Chain(self) -> bool:
        return isinstance(self, Chain_Chain)
    def Length(self):
        d_339___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (_this).is_Empty:
                    return (0) + (d_339___accumulator_)
                elif True:
                    d_339___accumulator_ = (((_this).v).Length()) + (d_339___accumulator_)
                    in63_ = (_this).previous
                    _this = in63_
                    
                    raise _dafny.TailCall()
                break

    def Count(self):
        d_340___accumulator_ = 0
        _this = self
        while True:
            with _dafny.label():
                if (_this).is_Empty:
                    return (0) + (d_340___accumulator_)
                elif True:
                    d_340___accumulator_ = (1) + (d_340___accumulator_)
                    in64_ = (_this).previous
                    _this = in64_
                    
                    raise _dafny.TailCall()
                break

    def Bytes(self):
        d_341___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        _this = self
        while True:
            with _dafny.label():
                if (_this).is_Empty:
                    return (_dafny.SeqWithoutIsStrInference([])) + (d_341___accumulator_)
                elif True:
                    d_341___accumulator_ = (((_this).v).Bytes()) + (d_341___accumulator_)
                    in65_ = (_this).previous
                    _this = in65_
                    
                    raise _dafny.TailCall()
                break

    def Append(self, v_k):
        if ((self).is_Chain) and (Std_JSON_Utils_Views_Core.default__.Adjacent((self).v, v_k)):
            return Chain_Chain((self).previous, Std_JSON_Utils_Views_Core.default__.Merge((self).v, v_k))
        elif True:
            return Chain_Chain(self, v_k)

    def CopyTo(self, dest, end):
        _this = self
        while True:
            with _dafny.label():
                if (_this).is_Chain:
                    d_342_end_: int
                    d_342_end_ = (end) - (((_this).v).Length())
                    ((_this).v).CopyTo(dest, d_342_end_)
                    in66_ = (_this).previous
                    in67_ = dest
                    in68_ = d_342_end_
                    _this = in66_
                    
                    dest = in67_
                    end = in68_
                    raise _dafny.TailCall()
                break


class Chain_Empty(Chain, NamedTuple('Empty', [])):
    def __dafnystr__(self) -> str:
        return f'Writers.Chain.Empty'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Chain_Empty)
    def __hash__(self) -> int:
        return super().__hash__()

class Chain_Chain(Chain, NamedTuple('Chain', [('previous', Any), ('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'Writers.Chain.Chain({_dafny.string_of(self.previous)}, {_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Chain_Chain) and self.previous == __o.previous and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()


class Writer:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Writer___Writer(0, Chain_Empty())

class Writer__:
    @classmethod
    def default(cls, ):
        return lambda: Writer___Writer(int(0), Chain.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Writer(self) -> bool:
        return isinstance(self, Writer___Writer)
    def Bytes(self):
        return ((self).chain).Bytes()

    @staticmethod
    def SaturatedAddU32(a, b):
        if (a) <= ((Std_BoundedInts.default__.UINT32__MAX) - (b)):
            return (a) + (b)
        elif True:
            return Std_BoundedInts.default__.UINT32__MAX

    def Append(self, v_k):
        return Writer___Writer(Writer__.SaturatedAddU32((self).length, (v_k).Length()), ((self).chain).Append(v_k))

    def Then(self, fn):
        return fn(self)

    def CopyTo(self, dest):
        ((self).chain).CopyTo(dest, (self).length)

    def ToArray(self):
        bs: _dafny.Array = _dafny.Array(None, 0)
        def lambda19_(d_343_i_):
            return 0

        init4_ = lambda19_
        nw5_ = _dafny.Array(None, (self).length)
        for i0_4_ in range(nw5_.length(0)):
            nw5_[i0_4_] = init4_(i0_4_)
        bs = nw5_
        (self).CopyTo(bs)
        return bs

    @_dafny.classproperty
    def Empty(instance):
        return Writer___Writer(0, Chain_Empty())
    @property
    def Unsaturated_q(self):
        return ((self).length) != (Std_BoundedInts.default__.UINT32__MAX)
    @property
    def Empty_q(self):
        return ((self).chain).is_Empty

class Writer___Writer(Writer__, NamedTuple('Writer', [('length', Any), ('chain', Any)])):
    def __dafnystr__(self) -> str:
        return f'Writers.Writer_.Writer({_dafny.string_of(self.length)}, {_dafny.string_of(self.chain)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Writer___Writer) and self.length == __o.length and self.chain == __o.chain
    def __hash__(self) -> int:
        return super().__hash__()

