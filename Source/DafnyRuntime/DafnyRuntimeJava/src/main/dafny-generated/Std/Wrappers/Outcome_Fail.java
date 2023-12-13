// Class Outcome_Fail<E>
// Dafny class Outcome_Fail<E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Outcome_Fail<E> extends Outcome<E> {
  public E _error;
  public Outcome_Fail (dafny.TypeDescriptor<E> _td_E, E error) {
    super(_td_E);
    this._error = error;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Outcome_Fail<E> o = (Outcome_Fail<E>)other;
    return true && java.util.Objects.equals(this._error, o._error);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 1;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._error);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Wrappers.Outcome.Fail");
    s.append("(");
    s.append(dafny.Helpers.toString(this._error));
    s.append(")");
    return s.toString();
  }
}
