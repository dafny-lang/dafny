// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Wrappers {

  public partial class __default {
    public static Std.Wrappers._IOutcomeResult<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Std.Wrappers.OutcomeResult<__E>.create_Pass_k();
      } else {
        return Std.Wrappers.OutcomeResult<__E>.create_Fail_k(error);
      }
    }
  }

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    bool IsFailure();
    Std.Wrappers._IOption<__U> PropagateFailure<__U>();
    T Extract();
    Std.Wrappers._IResult<T, __E> ToResult<__E>(__E error);
    Std.Wrappers._IOutcome<__E> ToOutcome<__E>(__E error);
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() {
    }
    public static Std.Wrappers._IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Wrappers._IOption<T>>(Std.Wrappers.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d)._value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public bool IsFailure() {
      return (this).is_None;
    }
    public Std.Wrappers._IOption<__U> PropagateFailure<__U>() {
      return Std.Wrappers.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
    public static T GetOr(Std.Wrappers._IOption<T> _this, T @default) {
      var _pat_let_tv0 = @default;
      Std.Wrappers._IOption<T> _source0 = _this;
      bool unmatched0 = true;
      if (unmatched0) {
        if (_source0.is_Some) {
          T v = _source0.dtor_value;
          unmatched0 = false;
          return v;
        }
      }
      if (unmatched0) {
        if (_source0.is_None) {
          unmatched0 = false;
          return _pat_let_tv0;
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public Std.Wrappers._IResult<T, __E> ToResult<__E>(__E error) {
      var _pat_let_tv1 = error;
      Std.Wrappers._IOption<T> _source1 = this;
      bool unmatched1 = true;
      if (unmatched1) {
        if (_source1.is_Some) {
          T v = _source1.dtor_value;
          unmatched1 = false;
          return Std.Wrappers.Result<T, __E>.create_Success(v);
        }
      }
      if (unmatched1) {
        if (_source1.is_None) {
          unmatched1 = false;
          return Std.Wrappers.Result<T, __E>.create_Failure(_pat_let_tv1);
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public Std.Wrappers._IOutcome<__E> ToOutcome<__E>(__E error) {
      var _pat_let_tv2 = error;
      Std.Wrappers._IOption<T> _source2 = this;
      bool unmatched2 = true;
      if (unmatched2) {
        if (_source2.is_Some) {
          T v = _source2.dtor_value;
          unmatched2 = false;
          return Std.Wrappers.Outcome<__E>.create_Pass();
        }
      }
      if (unmatched2) {
        if (_source2.is_None) {
          unmatched2 = false;
          return Std.Wrappers.Outcome<__E>.create_Fail(_pat_let_tv2);
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public static __FC Map<__FC>(Std.Wrappers._IOption<T> _this, Func<Std.Wrappers._IOption<T>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<Std.Wrappers._IOption<T>, __FC>>(rewrap)(_this);
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() : base() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _value;
    public Option_Some(T @value) : base() {
      this._value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Option_Some<T>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out R, out E> {
    bool is_Success { get; }
    bool is_Failure { get; }
    R dtor_value { get; }
    E dtor_error { get; }
    _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1);
    bool IsFailure();
    Std.Wrappers._IResult<__U, E> PropagateFailure<__U>();
    R Extract();
    Std.Wrappers._IOption<R> ToOption();
    Std.Wrappers._IOutcome<E> ToOutcome();
  }
  public abstract class Result<R, E> : _IResult<R, E> {
    public Result() {
    }
    public static Std.Wrappers._IResult<R, E> Default(R _default_R) {
      return create_Success(_default_R);
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IResult<R, E>> _TypeDescriptor(Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<Std.Wrappers._IResult<R, E>>(Std.Wrappers.Result<R, E>.Default(_td_R.Default()));
    }
    public static _IResult<R, E> create_Success(R @value) {
      return new Result_Success<R, E>(@value);
    }
    public static _IResult<R, E> create_Failure(E error) {
      return new Result_Failure<R, E>(error);
    }
    public bool is_Success { get { return this is Result_Success<R, E>; } }
    public bool is_Failure { get { return this is Result_Failure<R, E>; } }
    public R dtor_value {
      get {
        var d = this;
        return ((Result_Success<R, E>)d)._value;
      }
    }
    public E dtor_error {
      get {
        var d = this;
        return ((Result_Failure<R, E>)d)._error;
      }
    }
    public abstract _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1);
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Std.Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return Std.Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
    public R Extract() {
      return (this).dtor_value;
    }
    public static R GetOr(Std.Wrappers._IResult<R, E> _this, R @default) {
      var _pat_let_tv3 = @default;
      Std.Wrappers._IResult<R, E> _source3 = _this;
      bool unmatched3 = true;
      if (unmatched3) {
        if (_source3.is_Success) {
          R s = _source3.dtor_value;
          unmatched3 = false;
          return s;
        }
      }
      if (unmatched3) {
        if (_source3.is_Failure) {
          E e = _source3.dtor_error;
          unmatched3 = false;
          return _pat_let_tv3;
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public Std.Wrappers._IOption<R> ToOption() {
      Std.Wrappers._IResult<R, E> _source4 = this;
      bool unmatched4 = true;
      if (unmatched4) {
        if (_source4.is_Success) {
          R s = _source4.dtor_value;
          unmatched4 = false;
          return Std.Wrappers.Option<R>.create_Some(s);
        }
      }
      if (unmatched4) {
        if (_source4.is_Failure) {
          E _10_e = _source4.dtor_error;
          unmatched4 = false;
          return Std.Wrappers.Option<R>.create_None();
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public Std.Wrappers._IOutcome<E> ToOutcome() {
      Std.Wrappers._IResult<R, E> _source5 = this;
      bool unmatched5 = true;
      if (unmatched5) {
        if (_source5.is_Success) {
          R _11_s = _source5.dtor_value;
          unmatched5 = false;
          return Std.Wrappers.Outcome<E>.create_Pass();
        }
      }
      if (unmatched5) {
        if (_source5.is_Failure) {
          E _12_e = _source5.dtor_error;
          unmatched5 = false;
          return Std.Wrappers.Outcome<E>.create_Fail(_12_e);
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public static __FC Map<__FC>(Std.Wrappers._IResult<R, E> _this, Func<Std.Wrappers._IResult<R, E>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<Std.Wrappers._IResult<R, E>, __FC>>(rewrap)(_this);
    }
    public static Std.Wrappers._IResult<R, __NewE> MapFailure<__NewE>(Std.Wrappers._IResult<R, E> _this, Func<E, __NewE> reWrap) {
      var _pat_let_tv4 = reWrap;
      Std.Wrappers._IResult<R, E> _source6 = _this;
      bool unmatched6 = true;
      if (unmatched6) {
        if (_source6.is_Success) {
          R _13_s = _source6.dtor_value;
          unmatched6 = false;
          return Std.Wrappers.Result<R, __NewE>.create_Success(_13_s);
        }
      }
      if (unmatched6) {
        if (_source6.is_Failure) {
          E _14_e = _source6.dtor_error;
          unmatched6 = false;
          return Std.Wrappers.Result<R, __NewE>.create_Failure(Dafny.Helpers.Id<Func<E, __NewE>>(_pat_let_tv4)(_14_e));
        }
      }
      throw new System.Exception("unexpected control point");
    }
  }
  public class Result_Success<R, E> : Result<R, E> {
    public readonly R _value;
    public Result_Success(R @value) : base() {
      this._value = @value;
    }
    public override _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1) {
      if (this is _IResult<__R, __E> dt) { return dt; }
      return new Result_Success<__R, __E>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Result_Success<R, E>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<R, E> : Result<R, E> {
    public readonly E _error;
    public Result_Failure(E error) : base() {
      this._error = error;
    }
    public override _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1) {
      if (this is _IResult<__R, __E> dt) { return dt; }
      return new Result_Failure<__R, __E>(converter1(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Result_Failure<R, E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<out E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Std.Wrappers._IOutcome<E> PropagateFailure();
    Std.Wrappers._IOption<__R> ToOption<__R>(__R r);
    Std.Wrappers._IResult<__R, E> ToResult<__R>(__R r);
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() {
    }
    public static Std.Wrappers._IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Wrappers._IOutcome<E>>(Std.Wrappers.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d)._error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Std.Wrappers._IOutcome<E> PropagateFailure() {
      return this;
    }
    public Std.Wrappers._IOption<__R> ToOption<__R>(__R r) {
      var _pat_let_tv5 = r;
      Std.Wrappers._IOutcome<E> _source7 = this;
      bool unmatched7 = true;
      if (unmatched7) {
        if (_source7.is_Pass) {
          unmatched7 = false;
          return Std.Wrappers.Option<__R>.create_Some(_pat_let_tv5);
        }
      }
      if (unmatched7) {
        if (_source7.is_Fail) {
          E _15_e = _source7.dtor_error;
          unmatched7 = false;
          return Std.Wrappers.Option<__R>.create_None();
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public Std.Wrappers._IResult<__R, E> ToResult<__R>(__R r) {
      var _pat_let_tv6 = r;
      Std.Wrappers._IOutcome<E> _source8 = this;
      bool unmatched8 = true;
      if (unmatched8) {
        if (_source8.is_Pass) {
          unmatched8 = false;
          return Std.Wrappers.Result<__R, E>.create_Success(_pat_let_tv6);
        }
      }
      if (unmatched8) {
        if (_source8.is_Fail) {
          E _16_e = _source8.dtor_error;
          unmatched8 = false;
          return Std.Wrappers.Result<__R, E>.create_Failure(_16_e);
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public static __FC Map<__FC>(Std.Wrappers._IOutcome<E> _this, Func<Std.Wrappers._IOutcome<E>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<Std.Wrappers._IOutcome<E>, __FC>>(rewrap)(_this);
    }
    public static Std.Wrappers._IResult<__T, __NewE> MapFailure<__T, __NewE>(Std.Wrappers._IOutcome<E> _this, Func<E, __NewE> rewrap, __T @default)
    {
      var _pat_let_tv7 = @default;
      var _pat_let_tv8 = rewrap;
      Std.Wrappers._IOutcome<E> _source9 = _this;
      bool unmatched9 = true;
      if (unmatched9) {
        if (_source9.is_Pass) {
          unmatched9 = false;
          return Std.Wrappers.Result<__T, __NewE>.create_Success(_pat_let_tv7);
        }
      }
      if (unmatched9) {
        if (_source9.is_Fail) {
          E _17_e = _source9.dtor_error;
          unmatched9 = false;
          return Std.Wrappers.Result<__T, __NewE>.create_Failure(Dafny.Helpers.Id<Func<E, __NewE>>(_pat_let_tv8)(_17_e));
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public static Std.Wrappers._IOutcome<E> Need(bool condition, E error)
    {
      if (condition) {
        return Std.Wrappers.Outcome<E>.create_Pass();
      } else {
        return Std.Wrappers.Outcome<E>.create_Fail(error);
      }
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() : base() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E _error;
    public Outcome_Fail(E error) : base() {
      this._error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.Outcome_Fail<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcomeResult<out E> {
    bool is_Pass_k { get; }
    bool is_Fail_k { get; }
    E dtor_error { get; }
    _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Std.Wrappers._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class OutcomeResult<E> : _IOutcomeResult<E> {
    public OutcomeResult() {
    }
    public static Std.Wrappers._IOutcomeResult<E> Default() {
      return create_Pass_k();
    }
    public static Dafny.TypeDescriptor<Std.Wrappers._IOutcomeResult<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Std.Wrappers._IOutcomeResult<E>>(Std.Wrappers.OutcomeResult<E>.Default());
    }
    public static _IOutcomeResult<E> create_Pass_k() {
      return new OutcomeResult_Pass_k<E>();
    }
    public static _IOutcomeResult<E> create_Fail_k(E error) {
      return new OutcomeResult_Fail_k<E>(error);
    }
    public bool is_Pass_k { get { return this is OutcomeResult_Pass_k<E>; } }
    public bool is_Fail_k { get { return this is OutcomeResult_Fail_k<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((OutcomeResult_Fail_k<E>)d)._error;
      }
    }
    public abstract _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail_k;
    }
    public Std.Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return Std.Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class OutcomeResult_Pass_k<E> : OutcomeResult<E> {
    public OutcomeResult_Pass_k() : base() {
    }
    public override _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcomeResult<__E> dt) { return dt; }
      return new OutcomeResult_Pass_k<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.OutcomeResult_Pass_k<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.OutcomeResult.Pass'";
      return s;
    }
  }
  public class OutcomeResult_Fail_k<E> : OutcomeResult<E> {
    public readonly E _error;
    public OutcomeResult_Fail_k(E error) : base() {
      this._error = error;
    }
    public override _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcomeResult<__E> dt) { return dt; }
      return new OutcomeResult_Fail_k<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Std.Wrappers.OutcomeResult_Fail_k<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.OutcomeResult.Fail'";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }
} // end of namespace Std.Wrappers