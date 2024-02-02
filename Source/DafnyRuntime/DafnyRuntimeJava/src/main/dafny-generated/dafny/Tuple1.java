package dafny;

@SuppressWarnings({"unchecked", "deprecation"})
public class Tuple1<T0> {
  private T0 _0;

  public Tuple1(T0 _0) {
    this._0 = _0;
  }

  public static <T0> dafny.TypeDescriptor<Tuple1<T0>> _typeDescriptor(dafny.TypeDescriptor<T0> _td_T0) {
    return (dafny.TypeDescriptor<Tuple1<T0>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Tuple1.class, () -> Default(_td_T0.defaultValue()));
  }

  public static <T0> Tuple1<T0> Default(T0 _default_T0) {
    return create(_default_T0);
  }

  public static <T0> Tuple1<T0> create(T0 _0) {
    return new Tuple1(_0);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    Tuple1 o = (Tuple1) obj;
    return java.util.Objects.equals(this._0, o._0);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("(");
    sb.append(_0 == null ? "null" : _0.toString());
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
    return (int)hash;
  }

  public T0 dtor__0() { return this._0; }
}
