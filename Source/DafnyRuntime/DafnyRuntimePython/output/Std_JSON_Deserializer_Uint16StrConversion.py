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
import Std_JSON_Values
import Std_JSON_Errors
import Std_JSON_Spec
import Std_JSON_Utils_Views_Core
import Std_JSON_Utils_Views_Writers
import Std_JSON_Utils_Views
import Std_JSON_Utils_Lexers_Core
import Std_JSON_Utils_Lexers_Strings
import Std_JSON_Utils_Lexers
import Std_JSON_Utils_Cursors
import Std_JSON_Utils_Parsers
import Std_JSON_Utils
import Std_JSON_Grammar
import Std_JSON_ByteStrConversion
import Std_JSON_Serializer

# Module: Std_JSON_Deserializer_Uint16StrConversion

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
        d_455___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (digits) == (_dafny.SeqWithoutIsStrInference([])):
                    return (_dafny.SeqWithoutIsStrInference([])) + (d_455___accumulator_)
                elif True:
                    d_455___accumulator_ = (_dafny.SeqWithoutIsStrInference([(default__.chars)[(digits)[0]]])) + (d_455___accumulator_)
                    in81_ = _dafny.SeqWithoutIsStrInference((digits)[1::])
                    digits = in81_
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
        def lambda29_(forall_var_4_):
            d_456_c_: int = forall_var_4_
            return not ((d_456_c_) in (_dafny.SeqWithoutIsStrInference((str)[1::]))) or (default__.IsDigitChar(d_456_c_))

        return not ((str) != (_dafny.SeqWithoutIsStrInference([]))) or (((((str)[0]) == (minus)) or (((str)[0]) in (default__.charToDigit))) and (_dafny.quantifier((_dafny.SeqWithoutIsStrInference((str)[1::])).UniqueElements, True, lambda29_)))

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
            d_457_c_ = (str)[(len(str)) - (1)]
            return ((default__.ToNat(_dafny.SeqWithoutIsStrInference((str)[:(len(str)) - (1):]))) * (default__.base)) + ((default__.charToDigit)[d_457_c_])

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
        d_458___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (0) + (d_458___accumulator_)
                elif True:
                    d_458___accumulator_ = ((Std_Collections_Seq.default__.Last(xs)) * (Std_Arithmetic_Power.default__.Pow(default__.BASE(), (len(xs)) - (1)))) + (d_458___accumulator_)
                    in82_ = Std_Collections_Seq.default__.DropLast(xs)
                    xs = in82_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FromNat(n):
        d_459___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (d_459___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_459___accumulator_ = (d_459___accumulator_) + (_dafny.SeqWithoutIsStrInference([_dafny.euclidian_modulus(n, default__.BASE())]))
                    in83_ = _dafny.euclidian_division(n, default__.BASE())
                    n = in83_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqExtend(xs, n):
        while True:
            with _dafny.label():
                if (len(xs)) >= (n):
                    return xs
                elif True:
                    in84_ = (xs) + (_dafny.SeqWithoutIsStrInference([0]))
                    in85_ = n
                    xs = in84_
                    n = in85_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SeqExtendMultiple(xs, n):
        d_460_newLen_ = ((len(xs)) + (n)) - (_dafny.euclidian_modulus(len(xs), n))
        return default__.SeqExtend(xs, d_460_newLen_)

    @staticmethod
    def FromNatWithLen(n, len):
        return default__.SeqExtend(default__.FromNat(n), len)

    @staticmethod
    def SeqZero(len):
        d_461_xs_ = default__.FromNatWithLen(0, len)
        return d_461_xs_

    @staticmethod
    def SeqAdd(xs, ys):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            let_tmp_rhs13_ = default__.SeqAdd(Std_Collections_Seq.default__.DropLast(xs), Std_Collections_Seq.default__.DropLast(ys))
            d_462_zs_k_ = let_tmp_rhs13_[0]
            d_463_cin_ = let_tmp_rhs13_[1]
            d_464_sum_ = ((Std_Collections_Seq.default__.Last(xs)) + (Std_Collections_Seq.default__.Last(ys))) + (d_463_cin_)
            let_tmp_rhs14_ = ((d_464_sum_, 0) if (d_464_sum_) < (default__.BASE()) else ((d_464_sum_) - (default__.BASE()), 1))
            d_465_sum__out_ = let_tmp_rhs14_[0]
            d_466_cout_ = let_tmp_rhs14_[1]
            return ((d_462_zs_k_) + (_dafny.SeqWithoutIsStrInference([d_465_sum__out_])), d_466_cout_)

    @staticmethod
    def SeqSub(xs, ys):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), 0)
        elif True:
            let_tmp_rhs15_ = default__.SeqSub(Std_Collections_Seq.default__.DropLast(xs), Std_Collections_Seq.default__.DropLast(ys))
            d_467_zs_ = let_tmp_rhs15_[0]
            d_468_cin_ = let_tmp_rhs15_[1]
            let_tmp_rhs16_ = ((((Std_Collections_Seq.default__.Last(xs)) - (Std_Collections_Seq.default__.Last(ys))) - (d_468_cin_), 0) if (Std_Collections_Seq.default__.Last(xs)) >= ((Std_Collections_Seq.default__.Last(ys)) + (d_468_cin_)) else ((((default__.BASE()) + (Std_Collections_Seq.default__.Last(xs))) - (Std_Collections_Seq.default__.Last(ys))) - (d_468_cin_), 1))
            d_469_diff__out_ = let_tmp_rhs16_[0]
            d_470_cout_ = let_tmp_rhs16_[1]
            return ((d_467_zs_) + (_dafny.SeqWithoutIsStrInference([d_469_diff__out_])), d_470_cout_)

    @_dafny.classproperty
    def chars(instance):
        return _dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('0')), ord(_dafny.CodePoint('1')), ord(_dafny.CodePoint('2')), ord(_dafny.CodePoint('3')), ord(_dafny.CodePoint('4')), ord(_dafny.CodePoint('5')), ord(_dafny.CodePoint('6')), ord(_dafny.CodePoint('7')), ord(_dafny.CodePoint('8')), ord(_dafny.CodePoint('9')), ord(_dafny.CodePoint('a')), ord(_dafny.CodePoint('b')), ord(_dafny.CodePoint('c')), ord(_dafny.CodePoint('d')), ord(_dafny.CodePoint('e')), ord(_dafny.CodePoint('f')), ord(_dafny.CodePoint('A')), ord(_dafny.CodePoint('B')), ord(_dafny.CodePoint('C')), ord(_dafny.CodePoint('D')), ord(_dafny.CodePoint('E')), ord(_dafny.CodePoint('F'))])
    @_dafny.classproperty
    def base(instance):
        return len(default__.chars)
    @_dafny.classproperty
    def charToDigit(instance):
        return _dafny.Map({ord(_dafny.CodePoint('0')): 0, ord(_dafny.CodePoint('1')): 1, ord(_dafny.CodePoint('2')): 2, ord(_dafny.CodePoint('3')): 3, ord(_dafny.CodePoint('4')): 4, ord(_dafny.CodePoint('5')): 5, ord(_dafny.CodePoint('6')): 6, ord(_dafny.CodePoint('7')): 7, ord(_dafny.CodePoint('8')): 8, ord(_dafny.CodePoint('9')): 9, ord(_dafny.CodePoint('a')): 10, ord(_dafny.CodePoint('b')): 11, ord(_dafny.CodePoint('c')): 12, ord(_dafny.CodePoint('d')): 13, ord(_dafny.CodePoint('e')): 14, ord(_dafny.CodePoint('f')): 15, ord(_dafny.CodePoint('A')): 10, ord(_dafny.CodePoint('B')): 11, ord(_dafny.CodePoint('C')): 12, ord(_dafny.CodePoint('D')): 13, ord(_dafny.CodePoint('E')): 14, ord(_dafny.CodePoint('F')): 15})

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
