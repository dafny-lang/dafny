// Class Outcome<E>
// Dafny class Outcome<E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Outcome<E> {
  protected dafny.TypeDescriptor<E> _td_E;
  public Outcome(dafny.TypeDescriptor<E> _td_E) {
    this._td_E = _td_E;
  }

  public static <E> Outcome<E> Default(dafny.TypeDescriptor<E> _td_E) {
    return Std.Wrappers.Outcome.<E>create_Pass(_td_E);
  }
  public static <E> dafny.TypeDescriptor<Outcome<E>> _typeDescriptor(dafny.TypeDescriptor<E> _td_E) {
    return (dafny.TypeDescriptor<Outcome<E>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Outcome<E>>referenceWithInitializer(Outcome.class, () -> Outcome.<E>Default(_td_E));
  }
  public static <E> Outcome<E> create_Pass(dafny.TypeDescriptor<E> _td_E) {
    return new Outcome_Pass<E>(_td_E);
  }
  public static <E> Outcome<E> create_Fail(dafny.TypeDescriptor<E> _td_E, E error) {
    return new Outcome_Fail<E>(_td_E, error);
  }
  public boolean is_Pass() { return this instanceof Outcome_Pass; }
  public boolean is_Fail() { return this instanceof Outcome_Fail; }
  public E dtor_error() {
    Outcome<E> d = this;
    return ((Outcome_Fail<E>)d)._error;
  }
  public boolean IsFailure(dafny.TypeDescriptor<E> _td_E) {
    return (this).is_Fail();
  }
  public Outcome<E> PropagateFailure(dafny.TypeDescriptor<E> _td_E) {
    return this;
  }
  public <__R> Option<__R> ToOption(dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__R> _td___R, __R r)
  {
    Outcome<E> _source7 = this;
    if (_source7.is_Pass()) {
      return Std.Wrappers.Option.<__R>create_Some(_td___R, r);
    } else {
      E _22___mcc_h0 = ((Std.Wrappers.Outcome_Fail<E>)_source7)._error;
      E _23_e = _22___mcc_h0;
      return Std.Wrappers.Option.<__R>create_None(_td___R);
    }
  }
  public <__R> Result<__R, E> ToResult(dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__R> _td___R, __R r)
  {
    Outcome<E> _source8 = this;
    if (_source8.is_Pass()) {
      return Std.Wrappers.Result.<__R, E>create_Success(_td___R, _td_E, r);
    } else {
      E _24___mcc_h0 = ((Std.Wrappers.Outcome_Fail<E>)_source8)._error;
      E _25_e = _24___mcc_h0;
      return Std.Wrappers.Result.<__R, E>create_Failure(_td___R, _td_E, _25_e);
    }
  }
  public <__FC> __FC Map(dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__FC> _td___FC, java.util.function.Function<Outcome<E>, __FC> rewrap)
  {
    return ((__FC)(java.lang.Object)((rewrap).apply(this)));
  }
  public <__T, __NewE> Result<__T, __NewE> MapFailure(dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__T> _td___T, dafny.TypeDescriptor<__NewE> _td___NewE, java.util.function.Function<E, __NewE> rewrap, __T default_)
  {
    Outcome<E> _source9 = this;
    if (_source9.is_Pass()) {
      return Std.Wrappers.Result.<__T, __NewE>create_Success(_td___T, _td___NewE, default_);
    } else {
      E _26___mcc_h0 = ((Std.Wrappers.Outcome_Fail<E>)_source9)._error;
      E _27_e = _26___mcc_h0;
      return Std.Wrappers.Result.<__T, __NewE>create_Failure(_td___T, _td___NewE, ((__NewE)(java.lang.Object)((rewrap).apply(_27_e))));
    }
  }
  public static <E> Outcome<E> Need(dafny.TypeDescriptor<E> _td_E, boolean condition, E error)
  {
    if (condition) {
      return Std.Wrappers.Outcome.<E>create_Pass(_td_E);
    } else {
      return Std.Wrappers.Outcome.<E>create_Fail(_td_E, error);
    }
  }
}
