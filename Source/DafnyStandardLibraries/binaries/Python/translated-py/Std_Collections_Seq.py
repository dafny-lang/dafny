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

# Module: Std_Collections_Seq

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def First(xs):
        return (xs)[0]

    @staticmethod
    def DropFirst(xs):
        return _dafny.SeqWithoutIsStrInference((xs)[1::])

    @staticmethod
    def Last(xs):
        return (xs)[(len(xs)) - (1)]

    @staticmethod
    def DropLast(xs):
        return _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])

    @staticmethod
    def ToArray(xs):
        a: _dafny.Array = _dafny.Array(None, 0)
        def lambda3_(d_65_xs_):
            def lambda4_(d_66_i_):
                return (d_65_xs_)[d_66_i_]

            return lambda4_

        init2_ = lambda3_(xs)
        nw2_ = _dafny.Array(None, len(xs))
        for i0_2_ in range(nw2_.length(0)):
            nw2_[i0_2_] = init2_(i0_2_)
        a = nw2_
        return a

    @staticmethod
    def ToSet(xs):
        def iife0_():
            coll0_ = _dafny.Set()
            compr_0_: TypeVar('T__')
            for compr_0_ in (xs).Elements:
                d_67_x_: TypeVar('T__') = compr_0_
                if (d_67_x_) in (xs):
                    coll0_ = coll0_.union(_dafny.Set([d_67_x_]))
            return _dafny.Set(coll0_)
        return iife0_()
        

    @staticmethod
    def IndexOf(xs, v):
        d_68___accumulator_ = 0
        while True:
            with _dafny.label():
                if ((xs)[0]) == (v):
                    return (0) + (d_68___accumulator_)
                elif True:
                    d_68___accumulator_ = (d_68___accumulator_) + (1)
                    in0_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in1_ = v
                    xs = in0_
                    v = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def IndexOfOption(xs, v):
        if (len(xs)) == (0):
            return Std_Wrappers.Option_None()
        elif ((xs)[0]) == (v):
            return Std_Wrappers.Option_Some(0)
        elif True:
            d_69_o_k_ = default__.IndexOfOption(_dafny.SeqWithoutIsStrInference((xs)[1::]), v)
            if (d_69_o_k_).is_Some:
                return Std_Wrappers.Option_Some(((d_69_o_k_).value) + (1))
            elif True:
                return Std_Wrappers.Option_None()

    @staticmethod
    def LastIndexOf(xs, v):
        while True:
            with _dafny.label():
                if ((xs)[(len(xs)) - (1)]) == (v):
                    return (len(xs)) - (1)
                elif True:
                    in2_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in3_ = v
                    xs = in2_
                    v = in3_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def LastIndexOfOption(xs, v):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return Std_Wrappers.Option_None()
                elif ((xs)[(len(xs)) - (1)]) == (v):
                    return Std_Wrappers.Option_Some((len(xs)) - (1))
                elif True:
                    in4_ = _dafny.SeqWithoutIsStrInference((xs)[:(len(xs)) - (1):])
                    in5_ = v
                    xs = in4_
                    v = in5_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Remove(xs, pos):
        return (_dafny.SeqWithoutIsStrInference((xs)[:pos:])) + (_dafny.SeqWithoutIsStrInference((xs)[(pos) + (1)::]))

    @staticmethod
    def RemoveValue(xs, v):
        if (v) not in (xs):
            return xs
        elif True:
            d_70_i_ = default__.IndexOf(xs, v)
            return (_dafny.SeqWithoutIsStrInference((xs)[:d_70_i_:])) + (_dafny.SeqWithoutIsStrInference((xs)[(d_70_i_) + (1)::]))

    @staticmethod
    def Insert(xs, a, pos):
        return ((_dafny.SeqWithoutIsStrInference((xs)[:pos:])) + (_dafny.SeqWithoutIsStrInference([a]))) + (_dafny.SeqWithoutIsStrInference((xs)[pos::]))

    @staticmethod
    def Reverse(xs):
        d_71___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (xs) == (_dafny.SeqWithoutIsStrInference([])):
                    return (d_71___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_71___accumulator_ = (d_71___accumulator_) + (_dafny.SeqWithoutIsStrInference([(xs)[(len(xs)) - (1)]]))
                    in6_ = _dafny.SeqWithoutIsStrInference((xs)[0:(len(xs)) - (1):])
                    xs = in6_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Repeat(v, length):
        d_72___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (length) == (0):
                    return (d_72___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_72___accumulator_ = (d_72___accumulator_) + (_dafny.SeqWithoutIsStrInference([v]))
                    in7_ = v
                    in8_ = (length) - (1)
                    v = in7_
                    length = in8_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Unzip(xs):
        if (len(xs)) == (0):
            return (_dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([]))
        elif True:
            let_tmp_rhs0_ = default__.Unzip(default__.DropLast(xs))
            d_73_a_ = let_tmp_rhs0_[0]
            d_74_b_ = let_tmp_rhs0_[1]
            return ((d_73_a_) + (_dafny.SeqWithoutIsStrInference([(default__.Last(xs))[0]])), (d_74_b_) + (_dafny.SeqWithoutIsStrInference([(default__.Last(xs))[1]])))

    @staticmethod
    def Zip(xs, ys):
        d_75___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.SeqWithoutIsStrInference([])) + (d_75___accumulator_)
                elif True:
                    d_75___accumulator_ = (_dafny.SeqWithoutIsStrInference([(default__.Last(xs), default__.Last(ys))])) + (d_75___accumulator_)
                    in9_ = default__.DropLast(xs)
                    in10_ = default__.DropLast(ys)
                    xs = in9_
                    ys = in10_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Max(xs):
        if (len(xs)) == (1):
            return (xs)[0]
        elif True:
            return Std_Math.default__.Max((xs)[0], default__.Max(_dafny.SeqWithoutIsStrInference((xs)[1::])))

    @staticmethod
    def Min(xs):
        if (len(xs)) == (1):
            return (xs)[0]
        elif True:
            return Std_Math.default__.Min((xs)[0], default__.Min(_dafny.SeqWithoutIsStrInference((xs)[1::])))

    @staticmethod
    def Flatten(xs):
        d_76___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_76___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_76___accumulator_ = (d_76___accumulator_) + ((xs)[0])
                    in11_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    xs = in11_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FlattenReverse(xs):
        d_77___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (_dafny.SeqWithoutIsStrInference([])) + (d_77___accumulator_)
                elif True:
                    d_77___accumulator_ = (default__.Last(xs)) + (d_77___accumulator_)
                    in12_ = default__.DropLast(xs)
                    xs = in12_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Map(f, xs):
        d_78___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_78___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_78___accumulator_ = (d_78___accumulator_) + (_dafny.SeqWithoutIsStrInference([f((xs)[0])]))
                    in13_ = f
                    in14_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    f = in13_
                    xs = in14_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def MapWithResult(f, xs):
        if (len(xs)) == (0):
            return Std_Wrappers.Result_Success(_dafny.SeqWithoutIsStrInference([]))
        elif True:
            d_79_valueOrError0_ = f((xs)[0])
            if (d_79_valueOrError0_).IsFailure():
                return (d_79_valueOrError0_).PropagateFailure()
            elif True:
                d_80_head_ = (d_79_valueOrError0_).Extract()
                d_81_valueOrError1_ = default__.MapWithResult(f, _dafny.SeqWithoutIsStrInference((xs)[1::]))
                if (d_81_valueOrError1_).IsFailure():
                    return (d_81_valueOrError1_).PropagateFailure()
                elif True:
                    d_82_tail_ = (d_81_valueOrError1_).Extract()
                    return Std_Wrappers.Result_Success((_dafny.SeqWithoutIsStrInference([d_80_head_])) + (d_82_tail_))

    @staticmethod
    def Filter(f, xs):
        d_83___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_83___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_83___accumulator_ = (d_83___accumulator_) + ((_dafny.SeqWithoutIsStrInference([(xs)[0]]) if f((xs)[0]) else _dafny.SeqWithoutIsStrInference([])))
                    in15_ = f
                    in16_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    f = in15_
                    xs = in16_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FoldLeft(f, init, xs):
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return init
                elif True:
                    in17_ = f
                    in18_ = f(init, (xs)[0])
                    in19_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    f = in17_
                    init = in18_
                    xs = in19_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FoldRight(f, xs, init):
        if (len(xs)) == (0):
            return init
        elif True:
            return f((xs)[0], default__.FoldRight(f, _dafny.SeqWithoutIsStrInference((xs)[1::]), init))

    @staticmethod
    def SetToSeq(s):
        xs: _dafny.Seq = _dafny.Seq({})
        xs = _dafny.SeqWithoutIsStrInference([])
        d_84_left_: _dafny.Set
        d_84_left_ = s
        while (d_84_left_) != (_dafny.Set({})):
            d_85_x_: TypeVar('T__')
            with _dafny.label("_ASSIGN_SUCH_THAT_d_0"):
                assign_such_that_0_: TypeVar('T__')
                for assign_such_that_0_ in (d_84_left_).Elements:
                    d_85_x_ = assign_such_that_0_
                    if (d_85_x_) in (d_84_left_):
                        raise _dafny.Break("_ASSIGN_SUCH_THAT_d_0")
                raise Exception("assign-such-that search produced no value (line 7122)")
                pass
            d_84_left_ = (d_84_left_) - (_dafny.Set({d_85_x_}))
            xs = (xs) + (_dafny.SeqWithoutIsStrInference([d_85_x_]))
        return xs

    @staticmethod
    def SetToSortedSeq(s, R):
        xs: _dafny.Seq = _dafny.Seq({})
        out0_: _dafny.Seq
        out0_ = default__.SetToSeq(s)
        xs = out0_
        xs = default__.MergeSortBy(R, xs)
        return xs

    @staticmethod
    def MergeSortBy(lessThanOrEq, a):
        if (len(a)) <= (1):
            return a
        elif True:
            d_86_splitIndex_ = _dafny.euclidian_division(len(a), 2)
            d_87_left_ = _dafny.SeqWithoutIsStrInference((a)[:d_86_splitIndex_:])
            d_88_right_ = _dafny.SeqWithoutIsStrInference((a)[d_86_splitIndex_::])
            d_89_leftSorted_ = default__.MergeSortBy(lessThanOrEq, d_87_left_)
            d_90_rightSorted_ = default__.MergeSortBy(lessThanOrEq, d_88_right_)
            return default__.MergeSortedWith(d_89_leftSorted_, d_90_rightSorted_, lessThanOrEq)

    @staticmethod
    def MergeSortedWith(left, right, lessThanOrEq):
        d_91___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(left)) == (0):
                    return (d_91___accumulator_) + (right)
                elif (len(right)) == (0):
                    return (d_91___accumulator_) + (left)
                elif lessThanOrEq((left)[0], (right)[0]):
                    d_91___accumulator_ = (d_91___accumulator_) + (_dafny.SeqWithoutIsStrInference([(left)[0]]))
                    in20_ = _dafny.SeqWithoutIsStrInference((left)[1::])
                    in21_ = right
                    in22_ = lessThanOrEq
                    left = in20_
                    right = in21_
                    lessThanOrEq = in22_
                    raise _dafny.TailCall()
                elif True:
                    d_91___accumulator_ = (d_91___accumulator_) + (_dafny.SeqWithoutIsStrInference([(right)[0]]))
                    in23_ = left
                    in24_ = _dafny.SeqWithoutIsStrInference((right)[1::])
                    in25_ = lessThanOrEq
                    left = in23_
                    right = in24_
                    lessThanOrEq = in25_
                    raise _dafny.TailCall()
                break

