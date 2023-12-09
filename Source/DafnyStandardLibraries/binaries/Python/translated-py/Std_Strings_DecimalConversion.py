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

# Module: Std_Strings_DecimalConversion

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BASE():
        return default__.base

    @staticmethod
    def OfDigits(digits):
        d_136___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (digits) == (_dafny.SeqWithoutIsStrInference([])):
                    return (_dafny.SeqWithoutIsStrInference([])) + (d_136___accumulator_)
                elif True:
                    d_136___accumulator_ = (_dafny.SeqWithoutIsStrInference([(default__.chars)[(digits)[0]]])) + (d_136___accumulator_)
                    in47_ = _dafny.SeqWithoutIsStrInference((digits)[1::])
                    digits = in47_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def OfNat(n):
        if (n) == (0):
            return _dafny.SeqWithoutIsStrInference([(default__.chars)[0]])
        elif True:
            return default__.OfDigits(default__.FromNat(n))

    @staticmethod
    def OfNumberStr(str, minus):
        def lambda9_(forall_var_3_):
            d_137_c_: str = forall_var_3_
            return not ((d_137_c_) in (_dafny.SeqWithoutIsStrInference((str)[1::]))) or ((d_137_c_) in (default__.chars))

        return not ((str) != (_dafny.SeqWithoutIsStrInference([]))) or (((((str)[0]) == (minus)) or (((str)[0]) in (default__.chars))) and (_dafny.quantifier((_dafny.SeqWithoutIsStrInference((str)[1::])).UniqueElements, True, lambda9_)))

    @staticmethod
    def ToNumberStr(str, minus):
        def lambda10_(forall_var_4_):
            d_138_c_: str = forall_var_4_
            return not ((d_138_c_) in (_dafny.SeqWithoutIsStrInference((str)[1::]))) or ((d_138_c_) in (default__.charToDigit))

        return not ((str) != (_dafny.SeqWithoutIsStrInference([]))) or (((((str)[0]) == (minus)) or (((str)[0]) in (default__.charToDigit))) and (_dafny.quantifier((_dafny.SeqWithoutIsStrInference((str)[1::])).UniqueElements, True, lambda10_)))

    @staticmethod
    def OfInt(n, minus):
        if (n) >= (0):
            return default__.OfNat(n)
        elif True:
            return (_dafny.SeqWithoutIsStrInference([minus])) + (default__.OfNat((0) - (n)))

    @staticmethod
    def ToNat(str):
        if (str) == (_dafny.SeqWithoutIsStrInference([])):
            return 0
        elif True:
            return ((default__.ToNat(_dafny.SeqWithoutIsStrInference((str)[:(len(str)) - (1):]))) * (default__.base)) + ((default__.charToDigit)[(str)[(len(str)) - (1)]])

    @staticmethod
    def ToInt(str, minus):
        if (_dafny.SeqWithoutIsStrInference([minus])) <= (str):
            return (0) - (default__.ToNat(_dafny.SeqWithoutIsStrInference((str)[1::])))
        elif True:
            return default__.ToNat(str)

    @staticmethod
    def ToNatRight(xs):
        if (len(xs)) == (0):
            return 0
        elif True:
            return ((default__.ToNatRight(Std_Collections_Seq.default__.DropFirst(xs))) * (default__.BASE())) + (Std_Collections_Seq.default__.First(xs))

    @staticmethod
    def ToNatLeft(xs):
        d_139___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_139___accumulator_)
                elif True:
                    d_139___accumulator_ = ((Std_Collections_Seq.default__.Last(xs)) * (Std_Arithmetic_Power.default__.Pow(default__.BASE(), (len(xs)) - (1)))) + (d_139___accumulator_)
                    in48_ = Std_Collections_Seq.default__.DropLast(xs)
                    xs = in48_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FromNat(n):
        d_140___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (d_140___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_140___accumulator_ = (d_140___accumulator_) + (_dafny.SeqWithoutIsStrInference([_dafny.euclidian_modulus(n, default__.BASE())]))
                    in49_ = _dafny.euclidian_division(n, default__.BASE())
                    n = in49_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqExtend(xs, n):
        while True:
            with _dafny.label():
                if (len(xs)) >= (n):
                    return xs
                elif True:
                    in50_ = (xs) + (_dafny.SeqWithoutIsStrInference([0]))
                    in51_ = n
                    xs = in50_
                    n = in51_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqExtendMultiple(xs, n):
        d_141_newLen_ = ((len(xs)) + (n)) - (_dafny.euclidian_modulus(len(xs), n))
        return default__.SeqExtend(xs, d_141_newLen_)

    @staticmethod
    def FromNatWithLen(n, len):
        return default__.SeqExtend(default__.FromNat(n), len)

    @staticmethod
    def SeqZero(len):
        d_142_xs_ = default__.FromNatWithLen(0, len)
        return d_142_xs_

    @staticmethod
    def SeqAdd(xs, ys):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            let_tmp_rhs5_ = default__.SeqAdd(Std_Collections_Seq.default__.DropLast(xs), Std_Collections_Seq.default__.DropLast(ys))
            d_143_zs_k_ = let_tmp_rhs5_[0]
            d_144_cin_ = let_tmp_rhs5_[1]
            d_145_sum_ = ((Std_Collections_Seq.default__.Last(xs)) + (Std_Collections_Seq.default__.Last(ys))) + (d_144_cin_)
            let_tmp_rhs6_ = ((d_145_sum_, 0) if (d_145_sum_) < (default__.BASE()) else ((d_145_sum_) - (default__.BASE()), 1))
            d_146_sum__out_ = let_tmp_rhs6_[0]
            d_147_cout_ = let_tmp_rhs6_[1]
            return ((d_143_zs_k_) + (_dafny.SeqWithoutIsStrInference([d_146_sum__out_])), d_147_cout_)

    @staticmethod
    def SeqSub(xs, ys):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            let_tmp_rhs7_ = default__.SeqSub(Std_Collections_Seq.default__.DropLast(xs), Std_Collections_Seq.default__.DropLast(ys))
            d_148_zs_ = let_tmp_rhs7_[0]
            d_149_cin_ = let_tmp_rhs7_[1]
            let_tmp_rhs8_ = ((((Std_Collections_Seq.default__.Last(xs)) - (Std_Collections_Seq.default__.Last(ys))) - (d_149_cin_), 0) if (Std_Collections_Seq.default__.Last(xs)) >= ((Std_Collections_Seq.default__.Last(ys)) + (d_149_cin_)) else ((((default__.BASE()) + (Std_Collections_Seq.default__.Last(xs))) - (Std_Collections_Seq.default__.Last(ys))) - (d_149_cin_), 1))
            d_150_diff__out_ = let_tmp_rhs8_[0]
            d_151_cout_ = let_tmp_rhs8_[1]
            return ((d_148_zs_) + (_dafny.SeqWithoutIsStrInference([d_150_diff__out_])), d_151_cout_)

    @_dafny.classproperty
    def DIGITS(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0123456789"))
    @_dafny.classproperty
    def chars(instance):
        return default__.DIGITS
    @_dafny.classproperty
    def base(instance):
        return len(default__.chars)
    @_dafny.classproperty
    def charToDigit(instance):
        return _dafny.Map({_dafny.CodePoint('0'): 0, _dafny.CodePoint('1'): 1, _dafny.CodePoint('2'): 2, _dafny.CodePoint('3'): 3, _dafny.CodePoint('4'): 4, _dafny.CodePoint('5'): 5, _dafny.CodePoint('6'): 6, _dafny.CodePoint('7'): 7, _dafny.CodePoint('8'): 8, _dafny.CodePoint('9'): 9})

class CharSeq:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class digit:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
