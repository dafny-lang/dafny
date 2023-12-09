// Class Option_None<T>
// Dafny class Option_None<T> compiled into Java
package Std.Wrappers;


@SuppressWarnings({"unchecked", "deprecation"})
public class Option_None<T> extends Option<T> {
  public Option_None (dafny.TypeDescriptor<T> _td_T) {
    super(_td_T);
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Option_None<T> o = (Option_None<T>)other;
    return true;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Wrappers.Option.None");
    return s.toString();
  }
}
