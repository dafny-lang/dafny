// Class OutcomeResult_Fail_k<E>
// Dafny class OutcomeResult_Fail_k<E> compiled into Java
package Std.Wrappers;


@SuppressWarnings({"unchecked", "deprecation"})
public class OutcomeResult_Fail_k<E> extends OutcomeResult<E> {
  public E _error;
  public OutcomeResult_Fail_k (dafny.TypeDescriptor<E> _td_E, E error) {
    super(_td_E);
    this._error = error;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    OutcomeResult_Fail_k<E> o = (OutcomeResult_Fail_k<E>)other;
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
    s.append("Wrappers.OutcomeResult.Fail'");
    s.append("(");
    s.append(dafny.Helpers.toString(this._error));
    s.append(")");
    return s.toString();
  }
}
