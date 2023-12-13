// Class OutcomeResult<E>
// Dafny class OutcomeResult<E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class OutcomeResult<E> {
  protected dafny.TypeDescriptor<E> _td_E;
  public OutcomeResult(dafny.TypeDescriptor<E> _td_E) {
    this._td_E = _td_E;
  }

  public static <E> OutcomeResult<E> Default(dafny.TypeDescriptor<E> _td_E) {
    return Std.Wrappers.OutcomeResult.<E>create_Pass_k(_td_E);
  }
  public static <E> dafny.TypeDescriptor<OutcomeResult<E>> _typeDescriptor(dafny.TypeDescriptor<E> _td_E) {
    return (dafny.TypeDescriptor<OutcomeResult<E>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<OutcomeResult<E>>referenceWithInitializer(OutcomeResult.class, () -> OutcomeResult.<E>Default(_td_E));
  }
  public static <E> OutcomeResult<E> create_Pass_k(dafny.TypeDescriptor<E> _td_E) {
    return new OutcomeResult_Pass_k<E>(_td_E);
  }
  public static <E> OutcomeResult<E> create_Fail_k(dafny.TypeDescriptor<E> _td_E, E error) {
    return new OutcomeResult_Fail_k<E>(_td_E, error);
  }
  public boolean is_Pass_k() { return this instanceof OutcomeResult_Pass_k; }
  public boolean is_Fail_k() { return this instanceof OutcomeResult_Fail_k; }
  public E dtor_error() {
    OutcomeResult<E> d = this;
    return ((OutcomeResult_Fail_k<E>)d)._error;
  }
  public boolean IsFailure(dafny.TypeDescriptor<E> _td_E) {
    return (this).is_Fail_k();
  }
  public <__U> Result<__U, E> PropagateFailure(dafny.TypeDescriptor<E> _td_E, dafny.TypeDescriptor<__U> _td___U)
  {
    return Std.Wrappers.Result.<__U, E>create_Failure(_td___U, _td_E, (this).dtor_error());
  }
}
