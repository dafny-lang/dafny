// Class Result<R, E>
// Dafny class Result<R, E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Result<R, E> {
  protected dafny.TypeDescriptor<R> _td_R;
  protected dafny.TypeDescriptor<E> _td_E;
  public Result(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E) {
    this._td_R = _td_R;
    this._td_E = _td_E;
  }

  public static <R, E> Result<R, E> Default(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, R _default_R) {
    return Std.Wrappers.Result.<R, E>create_Success(_td_R, _td_E, _default_R);
  }
  public static <R, E> dafny.TypeDescriptor<Result<R, E>> _typeDescriptor(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E) {
    return (dafny.TypeDescriptor<Result<R, E>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Result<R, E>>referenceWithInitializer(Result.class, () -> Result.<R, E>Default(_td_R, _td_E, _td_R.defaultValue()));
  }
  public static <R, E> Result<R, E> create_Success(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, R value) {
    return new Result_Success<R, E>(_td_R, _td_E, value);
  }
  public static <R, E> Result<R, E> create_Failure(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, E error) {
    return new Result_Failure<R, E>(_td_R, _td_E, error);
  }
  public boolean is_Success() { return this instanceof Result_Success; }
  public boolean is_Failure() { return this instanceof Result_Failure; }
  public R dtor_value() {
    Result<R, E> d = this;
    return ((Result_Success<R, E>)d)._value;
  }
  public E dtor_error() {
    Result<R, E> d = this;
    return ((Result_Failure<R, E>)d)._error;
  }
  public boolean IsFailure(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E)
  {
    return (this).is_Failure();
  }
  public <__U> Result<__U, E> PropagateFailure(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__U> _td___U)
  {
    return Std.Wrappers.Result.<__U, E>create_Failure(_td___U, _td_E, (this).dtor_error());
  }
  public R Extract(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E)
  {
    return (this).dtor_value();
  }
  public R GetOr(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, R default_)
  {
    Result<R, E> _source3 = this;
    if (_source3.is_Success()) {
      R _6___mcc_h0 = ((Std.Wrappers.Result_Success<R, E>)_source3)._value;
      R _7_s = _6___mcc_h0;
      return _7_s;
    } else {
      E _8___mcc_h1 = ((Std.Wrappers.Result_Failure<R, E>)_source3)._error;
      E _9_e = _8___mcc_h1;
      return default_;
    }
  }
  public Option<R> ToOption(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E)
  {
    Result<R, E> _source4 = this;
    if (_source4.is_Success()) {
      R _10___mcc_h0 = ((Std.Wrappers.Result_Success<R, E>)_source4)._value;
      R _11_s = _10___mcc_h0;
      return Std.Wrappers.Option.<R>create_Some(_td_R, _11_s);
    } else {
      E _12___mcc_h1 = ((Std.Wrappers.Result_Failure<R, E>)_source4)._error;
      E _13_e = _12___mcc_h1;
      return Std.Wrappers.Option.<R>create_None(_td_R);
    }
  }
  public Outcome<E> ToOutcome(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E)
  {
    Result<R, E> _source5 = this;
    if (_source5.is_Success()) {
      R _14___mcc_h0 = ((Std.Wrappers.Result_Success<R, E>)_source5)._value;
      R _15_s = _14___mcc_h0;
      return Std.Wrappers.Outcome.<E>create_Pass(_td_E);
    } else {
      E _16___mcc_h1 = ((Std.Wrappers.Result_Failure<R, E>)_source5)._error;
      E _17_e = _16___mcc_h1;
      return Std.Wrappers.Outcome.<E>create_Fail(_td_E, _17_e);
    }
  }
  public <__FC> __FC Map(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__FC> _td___FC, java.util.function.Function<Result<R, E>, __FC> rewrap)
  {
    return ((__FC)(java.lang.Object)((rewrap).apply(this)));
  }
  public <__NewE> Result<R, __NewE> MapFailure(dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__NewE> _td___NewE, java.util.function.Function<E, __NewE> reWrap)
  {
    Result<R, E> _source6 = this;
    if (_source6.is_Success()) {
      R _18___mcc_h0 = ((Std.Wrappers.Result_Success<R, E>)_source6)._value;
      R _19_s = _18___mcc_h0;
      return Std.Wrappers.Result.<R, __NewE>create_Success(_td_R, _td___NewE, _19_s);
    } else {
      E _20___mcc_h1 = ((Std.Wrappers.Result_Failure<R, E>)_source6)._error;
      E _21_e = _20___mcc_h1;
      return Std.Wrappers.Result.<R, __NewE>create_Failure(_td_R, _td___NewE, ((__NewE)(java.lang.Object)((reWrap).apply(_21_e))));
    }
  }
}
