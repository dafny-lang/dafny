import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_

# Module: Std_Wrappers

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Need(condition, error):
        if condition:
            return OutcomeResult_Pass_k()
        elif True:
            return OutcomeResult_Fail_k(error)


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
    def IsFailure(self):
        return (self).is_None

    def PropagateFailure(self):
        return Option_None()

    def Extract(self):
        return (self).value

    def GetOr(self, default):
        source0_ = self
        if source0_.is_None:
            return default
        elif True:
            d_0___mcc_h0_ = source0_.value
            d_1_v_ = d_0___mcc_h0_
            return d_1_v_

    def ToResult(self, error):
        source1_ = self
        if source1_.is_None:
            return Result_Failure(error)
        elif True:
            d_2___mcc_h0_ = source1_.value
            d_3_v_ = d_2___mcc_h0_
            return Result_Success(d_3_v_)

    def ToOutcome(self, error):
        source2_ = self
        if source2_.is_None:
            return Outcome_Fail(error)
        elif True:
            d_4___mcc_h0_ = source2_.value
            d_5_v_ = d_4___mcc_h0_
            return Outcome_Pass()

    def Map(self, rewrap):
        return rewrap(self)


class Option_None(Option, NamedTuple('None_', [])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.Option.None'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_None)
    def __hash__(self) -> int:
        return super().__hash__()

class Option_Some(Option, NamedTuple('Some', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.Option.Some({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Option_Some) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class Result:
    @classmethod
    def default(cls, default_R):
        return lambda: Result_Success(default_R())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Success(self) -> bool:
        return isinstance(self, Result_Success)
    @property
    def is_Failure(self) -> bool:
        return isinstance(self, Result_Failure)
    def IsFailure(self):
        return (self).is_Failure

    def PropagateFailure(self):
        return Result_Failure((self).error)

    def Extract(self):
        return (self).value

    def GetOr(self, default):
        source3_ = self
        if source3_.is_Success:
            d_6___mcc_h0_ = source3_.value
            d_7_s_ = d_6___mcc_h0_
            return d_7_s_
        elif True:
            d_8___mcc_h1_ = source3_.error
            d_9_e_ = d_8___mcc_h1_
            return default

    def ToOption(self):
        source4_ = self
        if source4_.is_Success:
            d_10___mcc_h0_ = source4_.value
            d_11_s_ = d_10___mcc_h0_
            return Option_Some(d_11_s_)
        elif True:
            d_12___mcc_h1_ = source4_.error
            d_13_e_ = d_12___mcc_h1_
            return Option_None()

    def ToOutcome(self):
        source5_ = self
        if source5_.is_Success:
            d_14___mcc_h0_ = source5_.value
            d_15_s_ = d_14___mcc_h0_
            return Outcome_Pass()
        elif True:
            d_16___mcc_h1_ = source5_.error
            d_17_e_ = d_16___mcc_h1_
            return Outcome_Fail(d_17_e_)

    def Map(self, rewrap):
        return rewrap(self)

    def MapFailure(self, reWrap):
        source6_ = self
        if source6_.is_Success:
            d_18___mcc_h0_ = source6_.value
            d_19_s_ = d_18___mcc_h0_
            return Result_Success(d_19_s_)
        elif True:
            d_20___mcc_h1_ = source6_.error
            d_21_e_ = d_20___mcc_h1_
            return Result_Failure(reWrap(d_21_e_))


class Result_Success(Result, NamedTuple('Success', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.Result.Success({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Result_Success) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()

class Result_Failure(Result, NamedTuple('Failure', [('error', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.Result.Failure({_dafny.string_of(self.error)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Result_Failure) and self.error == __o.error
    def __hash__(self) -> int:
        return super().__hash__()


class Outcome:
    @classmethod
    def default(cls, ):
        return lambda: Outcome_Pass()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Pass(self) -> bool:
        return isinstance(self, Outcome_Pass)
    @property
    def is_Fail(self) -> bool:
        return isinstance(self, Outcome_Fail)
    def IsFailure(self):
        return (self).is_Fail

    def PropagateFailure(self):
        return self

    def ToOption(self, r):
        source7_ = self
        if source7_.is_Pass:
            return Option_Some(r)
        elif True:
            d_22___mcc_h0_ = source7_.error
            d_23_e_ = d_22___mcc_h0_
            return Option_None()

    def ToResult(self, r):
        source8_ = self
        if source8_.is_Pass:
            return Result_Success(r)
        elif True:
            d_24___mcc_h0_ = source8_.error
            d_25_e_ = d_24___mcc_h0_
            return Result_Failure(d_25_e_)

    def Map(self, rewrap):
        return rewrap(self)

    def MapFailure(self, rewrap, default):
        source9_ = self
        if source9_.is_Pass:
            return Result_Success(default)
        elif True:
            d_26___mcc_h0_ = source9_.error
            d_27_e_ = d_26___mcc_h0_
            return Result_Failure(rewrap(d_27_e_))

    @staticmethod
    def Need(condition, error):
        if condition:
            return Outcome_Pass()
        elif True:
            return Outcome_Fail(error)


class Outcome_Pass(Outcome, NamedTuple('Pass', [])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.Outcome.Pass'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Outcome_Pass)
    def __hash__(self) -> int:
        return super().__hash__()

class Outcome_Fail(Outcome, NamedTuple('Fail', [('error', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.Outcome.Fail({_dafny.string_of(self.error)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Outcome_Fail) and self.error == __o.error
    def __hash__(self) -> int:
        return super().__hash__()


class OutcomeResult:
    @classmethod
    def default(cls, ):
        return lambda: OutcomeResult_Pass_k()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Pass_k(self) -> bool:
        return isinstance(self, OutcomeResult_Pass_k)
    @property
    def is_Fail_k(self) -> bool:
        return isinstance(self, OutcomeResult_Fail_k)
    def IsFailure(self):
        return (self).is_Fail_k

    def PropagateFailure(self):
        return Result_Failure((self).error)


class OutcomeResult_Pass_k(OutcomeResult, NamedTuple('Pass_k', [])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.OutcomeResult.Pass\''
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, OutcomeResult_Pass_k)
    def __hash__(self) -> int:
        return super().__hash__()

class OutcomeResult_Fail_k(OutcomeResult, NamedTuple('Fail_k', [('error', Any)])):
    def __dafnystr__(self) -> str:
        return f'Wrappers.OutcomeResult.Fail\'({_dafny.string_of(self.error)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, OutcomeResult_Fail_k) and self.error == __o.error
    def __hash__(self) -> int:
        return super().__hash__()

