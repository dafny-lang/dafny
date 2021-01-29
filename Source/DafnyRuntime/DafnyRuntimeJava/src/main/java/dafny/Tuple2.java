// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

@SuppressWarnings({"unchecked", "deprecation"})
public class Tuple2<T0, T1> {
  private T0 _0;
  private T1 _1;

  public Tuple2(T0 _0, T1 _1) {
    this._0 = _0;
    this._1 = _1;
  }

  public static <T0, T1> dafny.TypeDescriptor<Tuple2<T0, T1>> _typeDescriptor(dafny.TypeDescriptor<T0> _td_T0, dafny.TypeDescriptor<T1> _td_T1) {
    return (dafny.TypeDescriptor<Tuple2<T0, T1>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Tuple2.class, () -> Default(_td_T0.defaultValue(), _td_T1.defaultValue()));
  }

  public static <T0, T1> Tuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
    return create(_default_T0, _default_T1);
  }

  public static <T0, T1> Tuple2<T0, T1> create(T0 _0, T1 _1) {
    return new Tuple2(_0, _1);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    Tuple2 o = (Tuple2) obj;
    return java.util.Objects.equals(this._0, o._0) && java.util.Objects.equals(this._1, o._1);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    sb.append(_0 == null ? "null" : _0.toString());
    sb.append(", ");
    sb.append(_1 == null ? "null" : _1.toString());
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
    return (int)hash;
  }

  public T0 dtor__0() { return this._0; }

  public T1 dtor__1() { return this._1; }
}
