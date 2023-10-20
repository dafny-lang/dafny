// Class ___hTotalFunc2
// Dafny class ___hTotalFunc2 compiled into Java
package _System;


@SuppressWarnings({"unchecked", "deprecation"})
public class ___hTotalFunc2<T0, T1, R> {
  protected dafny.TypeDescriptor<T0> _td_T0;
  protected dafny.TypeDescriptor<T1> _td_T1;
  protected dafny.TypeDescriptor<R> _td_R;
  public ___hTotalFunc2() {
    this._td_T0 = _td_T0;
    this._td_T1 = _td_T1;
    this._td_R = _td_R;
  }
  public static <T0, T1, R> dafny.TypeDescriptor<dafny.Function2<T0, T1, R>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.Function2<T0, T1, R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<dafny.Function2<T0, T1, R>>referenceWithInitializer(dafny.Function2.class, () -> ((T0 x0, T1 x1) -> _td_R.defaultValue()));
  }
}
