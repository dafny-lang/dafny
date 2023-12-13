// Class Option<T>
// Dafny class Option<T> compiled into Java
package Std.Wrappers;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Option<T> {
  protected dafny.TypeDescriptor<T> _td_T;
  public Option(dafny.TypeDescriptor<T> _td_T) {
    this._td_T = _td_T;
  }

  public static <T> Option<T> Default(dafny.TypeDescriptor<T> _td_T) {
    return Std.Wrappers.Option.<T>create_None(_td_T);
  }
  public static <T> dafny.TypeDescriptor<Option<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<Option<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Option<T>>referenceWithInitializer(Option.class, () -> Option.<T>Default(_td_T));
  }
  public static <T> Option<T> create_None(dafny.TypeDescriptor<T> _td_T) {
    return new Option_None<T>(_td_T);
  }
  public static <T> Option<T> create_Some(dafny.TypeDescriptor<T> _td_T, T value) {
    return new Option_Some<T>(_td_T, value);
  }
  public boolean is_None() { return this instanceof Option_None; }
  public boolean is_Some() { return this instanceof Option_Some; }
  public T dtor_value() {
    Option<T> d = this;
    return ((Option_Some<T>)d)._value;
  }
  public boolean IsFailure(dafny.TypeDescriptor<T> _td_T) {
    return (this).is_None();
  }
  public <__U> Option<__U> PropagateFailure(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<__U> _td___U)
  {
    return Std.Wrappers.Option.<__U>create_None(_td___U);
  }
  public T Extract(dafny.TypeDescriptor<T> _td_T) {
    return (this).dtor_value();
  }
  public T GetOr(dafny.TypeDescriptor<T> _td_T, T default_)
  {
    Option<T> _source0 = this;
    if (_source0.is_None()) {
      return default_;
    } else {
      T _0___mcc_h0 = ((Std.Wrappers.Option_Some<T>)_source0)._value;
      T _1_v = _0___mcc_h0;
      return _1_v;
    }
  }
  public <__E> Result<T, __E> ToResult(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<__E> _td___E, __E error)
  {
    Option<T> _source1 = this;
    if (_source1.is_None()) {
      return Std.Wrappers.Result.<T, __E>create_Failure(_td_T, _td___E, error);
    } else {
      T _2___mcc_h0 = ((Std.Wrappers.Option_Some<T>)_source1)._value;
      T _3_v = _2___mcc_h0;
      return Std.Wrappers.Result.<T, __E>create_Success(_td_T, _td___E, _3_v);
    }
  }
  public <__E> Outcome<__E> ToOutcome(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<__E> _td___E, __E error)
  {
    Option<T> _source2 = this;
    if (_source2.is_None()) {
      return Std.Wrappers.Outcome.<__E>create_Fail(_td___E, error);
    } else {
      T _4___mcc_h0 = ((Std.Wrappers.Option_Some<T>)_source2)._value;
      T _5_v = _4___mcc_h0;
      return Std.Wrappers.Outcome.<__E>create_Pass(_td___E);
    }
  }
  public <__FC> __FC Map(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<__FC> _td___FC, java.util.function.Function<Option<T>, __FC> rewrap)
  {
    return ((__FC)(java.lang.Object)((rewrap).apply(this)));
  }
}
