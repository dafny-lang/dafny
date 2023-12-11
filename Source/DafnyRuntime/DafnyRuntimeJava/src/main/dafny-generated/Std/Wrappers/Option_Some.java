// Class Option_Some<T>
// Dafny class Option_Some<T> compiled into Java
package Std.Wrappers;


@SuppressWarnings({"unchecked", "deprecation"})
public class Option_Some<T> extends Option<T> {
  public T _value;
  public Option_Some (dafny.TypeDescriptor<T> _td_T, T value) {
    super(_td_T);
    this._value = value;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Option_Some<T> o = (Option_Some<T>)other;
    return true && java.util.Objects.equals(this._value, o._value);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 1;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._value);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Wrappers.Option.Some");
    s.append("(");
    s.append(dafny.Helpers.toString(this._value));
    s.append(")");
    return s.toString();
  }
}
