// Class Outcome_Pass<E>
// Dafny class Outcome_Pass<E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Outcome_Pass<E> extends Outcome<E> {
  public Outcome_Pass (dafny.TypeDescriptor<E> _td_E) {
    super(_td_E);
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Outcome_Pass<E> o = (Outcome_Pass<E>)other;
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
    s.append("Wrappers.Outcome.Pass");
    return s.toString();
  }
}
