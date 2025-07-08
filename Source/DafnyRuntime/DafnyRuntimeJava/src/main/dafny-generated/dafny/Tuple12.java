package dafny;

@SuppressWarnings({"unchecked", "deprecation"})
public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
  private T0 _0;
  private T1 _1;
  private T2 _2;
  private T3 _3;
  private T4 _4;
  private T5 _5;
  private T6 _6;
  private T7 _7;
  private T8 _8;
  private T9 _9;
  private T10 _10;
  private T11 _11;

  public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
    this._0 = _0;
    this._1 = _1;
    this._2 = _2;
    this._3 = _3;
    this._4 = _4;
    this._5 = _5;
    this._6 = _6;
    this._7 = _7;
    this._8 = _8;
    this._9 = _9;
    this._10 = _10;
    this._11 = _11;
  }

  public static <T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> dafny.TypeDescriptor<Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _typeDescriptor(dafny.TypeDescriptor<T0> _td_T0, dafny.TypeDescriptor<T1> _td_T1, dafny.TypeDescriptor<T2> _td_T2, dafny.TypeDescriptor<T3> _td_T3, dafny.TypeDescriptor<T4> _td_T4, dafny.TypeDescriptor<T5> _td_T5, dafny.TypeDescriptor<T6> _td_T6, dafny.TypeDescriptor<T7> _td_T7, dafny.TypeDescriptor<T8> _td_T8, dafny.TypeDescriptor<T9> _td_T9, dafny.TypeDescriptor<T10> _td_T10, dafny.TypeDescriptor<T11> _td_T11) {
    return (dafny.TypeDescriptor<Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Tuple12.class, () -> Default(_td_T0.defaultValue(), _td_T1.defaultValue(), _td_T2.defaultValue(), _td_T3.defaultValue(), _td_T4.defaultValue(), _td_T5.defaultValue(), _td_T6.defaultValue(), _td_T7.defaultValue(), _td_T8.defaultValue(), _td_T9.defaultValue(), _td_T10.defaultValue(), _td_T11.defaultValue()));
  }

  public static <T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
    return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
  }

  public static <T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
    return new Tuple12(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    Tuple12 o = (Tuple12) obj;
    return java.util.Objects.equals(this._0, o._0) && java.util.Objects.equals(this._1, o._1) && java.util.Objects.equals(this._2, o._2) && java.util.Objects.equals(this._3, o._3) && java.util.Objects.equals(this._4, o._4) && java.util.Objects.equals(this._5, o._5) && java.util.Objects.equals(this._6, o._6) && java.util.Objects.equals(this._7, o._7) && java.util.Objects.equals(this._8, o._8) && java.util.Objects.equals(this._9, o._9) && java.util.Objects.equals(this._10, o._10) && java.util.Objects.equals(this._11, o._11);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    sb.append(_0 == null ? "null" : _0.toString());
    sb.append(", ");
    sb.append(_1 == null ? "null" : _1.toString());
    sb.append(", ");
    sb.append(_2 == null ? "null" : _2.toString());
    sb.append(", ");
    sb.append(_3 == null ? "null" : _3.toString());
    sb.append(", ");
    sb.append(_4 == null ? "null" : _4.toString());
    sb.append(", ");
    sb.append(_5 == null ? "null" : _5.toString());
    sb.append(", ");
    sb.append(_6 == null ? "null" : _6.toString());
    sb.append(", ");
    sb.append(_7 == null ? "null" : _7.toString());
    sb.append(", ");
    sb.append(_8 == null ? "null" : _8.toString());
    sb.append(", ");
    sb.append(_9 == null ? "null" : _9.toString());
    sb.append(", ");
    sb.append(_10 == null ? "null" : _10.toString());
    sb.append(", ");
    sb.append(_11 == null ? "null" : _11.toString());
    sb.append(")");
    return sb.toString();
  }

  @Override
  public int hashCode() {
    // GetHashCode method (Uses the djb2 algorithm)
    // https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._0);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._1);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._2);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._3);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._4);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._5);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._6);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._7);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._8);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._9);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._10);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._11);
    return (int)hash;
  }

  public T0 dtor__0() { return this._0; }

  public T1 dtor__1() { return this._1; }

  public T2 dtor__2() { return this._2; }

  public T3 dtor__3() { return this._3; }

  public T4 dtor__4() { return this._4; }

  public T5 dtor__5() { return this._5; }

  public T6 dtor__6() { return this._6; }

  public T7 dtor__7() { return this._7; }

  public T8 dtor__8() { return this._8; }

  public T9 dtor__9() { return this._9; }

  public T10 dtor__10() { return this._10; }

  public T11 dtor__11() { return this._11; }
}
