package dafny;

@SuppressWarnings({"unchecked", "deprecation"})
public class Tuple5<T0, T1, T2, T3, T4> {
  private T0 _0;
  private T1 _1;
  private T2 _2;
  private T3 _3;
  private T4 _4;

  public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
    this._0 = _0;
    this._1 = _1;
    this._2 = _2;
    this._3 = _3;
    this._4 = _4;
  }

  public static <T0, T1, T2, T3, T4> dafny.TypeDescriptor<Tuple5<T0, T1, T2, T3, T4>> _typeDescriptor(dafny.TypeDescriptor<T0> _td_T0, dafny.TypeDescriptor<T1> _td_T1, dafny.TypeDescriptor<T2> _td_T2, dafny.TypeDescriptor<T3> _td_T3, dafny.TypeDescriptor<T4> _td_T4) {
    return (dafny.TypeDescriptor<Tuple5<T0, T1, T2, T3, T4>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Tuple5.class, () -> Default(_td_T0.defaultValue(), _td_T1.defaultValue(), _td_T2.defaultValue(), _td_T3.defaultValue(), _td_T4.defaultValue()));
  }

  public static <T0, T1, T2, T3, T4> Tuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
    return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
  }

  public static <T0, T1, T2, T3, T4> Tuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
    return new Tuple5(_0, _1, _2, _3, _4);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    Tuple5 o = (Tuple5) obj;
    return java.util.Objects.equals(this._0, o._0) && java.util.Objects.equals(this._1, o._1) && java.util.Objects.equals(this._2, o._2) && java.util.Objects.equals(this._3, o._3) && java.util.Objects.equals(this._4, o._4);
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
    return (int)hash;
  }

  public T0 dtor__0() { return this._0; }

  public T1 dtor__1() { return this._1; }

  public T2 dtor__2() { return this._2; }

  public T3 dtor__3() { return this._3; }

  public T4 dtor__4() { return this._4; }
}
