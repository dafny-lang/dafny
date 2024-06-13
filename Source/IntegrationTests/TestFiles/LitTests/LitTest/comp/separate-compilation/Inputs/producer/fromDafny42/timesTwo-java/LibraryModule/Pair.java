// Class Pair<T, U>
// Dafny class Pair<T, U> compiled into Java
package LibraryModule;


@SuppressWarnings({"unchecked", "deprecation"})
public class Pair<T, U> {
  public T _first;
  public U _second;
  public Pair (T first, U second) {
    this._first = first;
    this._second = second;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Pair<T, U> o = (Pair<T, U>)other;
    return true && java.util.Objects.equals(this._first, o._first) && java.util.Objects.equals(this._second, o._second);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._first);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._second);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("LibraryModule.Pair.Pair");
    s.append("(");
    s.append(dafny.Helpers.toString(this._first));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._second));
    s.append(")");
    return s.toString();
  }

  public static <T, U> Pair<T, U> Default(T _default_T, U _default_U) {
    dafny.TypeDescriptor<T> _td_T = (dafny.TypeDescriptor<T>)dafny.TypeDescriptor.OBJECT;
    dafny.TypeDescriptor<U> _td_U = (dafny.TypeDescriptor<U>)dafny.TypeDescriptor.OBJECT;
    return LibraryModule.Pair.<T, U>create(_default_T, _default_U);
  }
  public static <T, U> dafny.TypeDescriptor<Pair<T, U>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<U> _td_U) {
    return (dafny.TypeDescriptor<Pair<T, U>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<Pair<T, U>>referenceWithInitializer(Pair.class, () -> Default(_td_T.defaultValue(), _td_U.defaultValue()));
  }
  public static <T, U> Pair<T, U> create(T first, U second) {
    return new Pair<T, U>(first, second);
  }
  public static <T, U> Pair<T, U> create_Pair(T first, U second) {
    return create(first, second);
  }
  public boolean is_Pair() { return true; }
  public T dtor_first() {
    return this._first;
  }
  public U dtor_second() {
    return this._second;
  }
}
