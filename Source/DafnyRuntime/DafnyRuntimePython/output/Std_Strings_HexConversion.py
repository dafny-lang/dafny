import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Std_Wrappers
import Std_Concurrent
import Std_FileIOInternalExterns
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

# Module: Std_Strings_HexConversion

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def BASE():
        return default__.base

    @staticmethod
    def IsDigitChar(c):
        return (c) in (default__.charToDigit)

    @staticmethod
    def OfDigits(digits):
        d_130___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (digits) == (_dafny.SeqWithoutIsStrInference([])):
                    return (_dafny.SeqWithoutIsStrInference([])) + (d_130___accumulator_)
                elif True:
                    d_130___accumulator_ = (_dafny.SeqWithoutIsStrInference([(default__.chars)[(digits)[0]]])) + (d_130___accumulator_)
                    in46_ = _dafny.SeqWithoutIsStrInference((digits)[1::])
                    digits = in46_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def OfNat(n):
        if (n) == (0):
            return _dafny.SeqWithoutIsStrInference([(default__.chars)[0]])
        elif True:
            return default__.OfDigits(default__.FromNat(n))

    @staticmethod
    def IsNumberStr(str, minus):
        def lambda11_(forall_var_1_):
            d_131_c_: str = forall_var_1_
            return not ((d_131_c_) in (_dafny.SeqWithoutIsStrInference((str)[1::]))) or (default__.IsDigitChar(d_131_c_))

        return not ((str) != (_dafny.SeqWithoutIsStrInference([]))) or (((((str)[0]) == (minus)) or (((str)[0]) in (default__.charToDigit))) and (_dafny.quantifier((_dafny.SeqWithoutIsStrInference((str)[1::])).UniqueElements, True, lambda11_)))

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
            d_132_c_ = (str)[(len(str)) - (1)]
            return ((default__.ToNat(_dafny.SeqWithoutIsStrInference((str)[:(len(str)) - (1):]))) * (default__.base)) + ((default__.charToDigit)[d_132_c_])

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
        d_133___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_133___accumulator_)
                elif True:
                    d_133___accumulator_ = ((Std_Collections_Seq.default__.Last(xs)) * (Std_Arithmetic_Power.default__.Pow(default__.BASE(), (len(xs)) - (1)))) + (d_133___accumulator_)
                    in47_ = Std_Collections_Seq.default__.DropLast(xs)
                    xs = in47_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FromNat(n):
        d_134___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (d_134___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_134___accumulator_ = (d_134___accumulator_) + (_dafny.SeqWithoutIsStrInference([_dafny.euclidian_modulus(n, default__.BASE())]))
                    in48_ = _dafny.euclidian_division(n, default__.BASE())
                    n = in48_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqExtend(xs, n):
        while True:
            with _dafny.label():
                if (len(xs)) >= (n):
                    return xs
                elif True:
                    in49_ = (xs) + (_dafny.SeqWithoutIsStrInference([0]))
                    in50_ = n
                    xs = in49_
                    n = in50_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqExtendMultiple(xs, n):
        d_135_newLen_ = ((len(xs)) + (n)) - (_dafny.euclidian_modulus(len(xs), n))
        return default__.SeqExtend(xs, d_135_newLen_)

    @staticmethod
    def FromNatWithLen(n, len):
        return default__.SeqExtend(default__.FromNat(n), len)

    @staticmethod
    def SeqZero(len):
        d_136_xs_ = default__.FromNatWithLen(0, len)
        return d_136_xs_

    @staticmethod
    def SeqAdd(xs, ys):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            let_tmp_rhs1_ = default__.SeqAdd(Std_Collections_Seq.default__.DropLast(xs), Std_Collections_Seq.default__.DropLast(ys))
            d_137_zs_k_ = let_tmp_rhs1_[0]
            d_138_cin_ = let_tmp_rhs1_[1]
            d_139_sum_ = ((Std_Collections_Seq.default__.Last(xs)) + (Std_Collections_Seq.default__.Last(ys))) + (d_138_cin_)
            let_tmp_rhs2_ = ((d_139_sum_, 0) if (d_139_sum_) < (default__.BASE()) else ((d_139_sum_) - (default__.BASE()), 1))
            d_140_sum__out_ = let_tmp_rhs2_[0]
            d_141_cout_ = let_tmp_rhs2_[1]
            return ((d_137_zs_k_) + (_dafny.SeqWithoutIsStrInference([d_140_sum__out_])), d_141_cout_)

    @staticmethod
    def SeqSub(xs, ys):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            let_tmp_rhs3_ = default__.SeqSub(Std_Collections_Seq.default__.DropLast(xs), Std_Collections_Seq.default__.DropLast(ys))
            d_142_zs_ = let_tmp_rhs3_[0]
            d_143_cin_ = let_tmp_rhs3_[1]
            let_tmp_rhs4_ = ((((Std_Collections_Seq.default__.Last(xs)) - (Std_Collections_Seq.default__.Last(ys))) - (d_143_cin_), 0) if (Std_Collections_Seq.default__.Last(xs)) >= ((Std_Collections_Seq.default__.Last(ys)) + (d_143_cin_)) else ((((default__.BASE()) + (Std_Collections_Seq.default__.Last(xs))) - (Std_Collections_Seq.default__.Last(ys))) - (d_143_cin_), 1))
            d_144_diff__out_ = let_tmp_rhs4_[0]
            d_145_cout_ = let_tmp_rhs4_[1]
            return ((d_142_zs_) + (_dafny.SeqWithoutIsStrInference([d_144_diff__out_])), d_145_cout_)

    @_dafny.classproperty
    def HEX__DIGITS(instance):
        return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0123456789ABCDEF"))
    @_dafny.classproperty
    def chars(instance):
        return default__.HEX__DIGITS
    @_dafny.classproperty
    def base(instance):
        return len(default__.chars)
    @_dafny.classproperty
    def charToDigit(instance):
        return _dafny.Map({_dafny.CodePoint('0'): 0, _dafny.CodePoint('1'): 1, _dafny.CodePoint('2'): 2, _dafny.CodePoint('3'): 3, _dafny.CodePoint('4'): 4, _dafny.CodePoint('5'): 5, _dafny.CodePoint('6'): 6, _dafny.CodePoint('7'): 7, _dafny.CodePoint('8'): 8, _dafny.CodePoint('9'): 9, _dafny.CodePoint('a'): 10, _dafny.CodePoint('b'): 11, _dafny.CodePoint('c'): 12, _dafny.CodePoint('d'): 13, _dafny.CodePoint('e'): 14, _dafny.CodePoint('f'): 15, _dafny.CodePoint('A'): 10, _dafny.CodePoint('B'): 11, _dafny.CodePoint('C'): 12, _dafny.CodePoint('D'): 13, _dafny.CodePoint('E'): 14, _dafny.CodePoint('F'): 15})

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
