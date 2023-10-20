// Class ___hTotalFunc3
// Dafny class ___hTotalFunc3 compiled into Java
package _System;


@SuppressWarnings({"unchecked", "deprecation"})
public class ___hTotalFunc3<T0, T1, T2, R> {
  protected dafny.TypeDescriptor<T0> _td_T0;
  protected dafny.TypeDescriptor<T1> _td_T1;
  protected dafny.TypeDescriptor<T2> _td_T2;
  protected dafny.TypeDescriptor<R> _td_R;
  public ___hTotalFunc3() {
    this._td_T0 = _td_T0;
    this._td_T1 = _td_T1;
    this._td_T2 = _td_T2;
    this._td_R = _td_R;
  }
  public static <T0, T1, T2, R> dafny.TypeDescriptor<dafny.Function3<T0, T1, T2, R>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.Function3<T0, T1, T2, R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<dafny.Function3<T0, T1, T2, R>>referenceWithInitializer(dafny.Function3.class, () -> ((T0 x0, T1 x1, T2 x2) -> _td_R.defaultValue()));
  }
}
