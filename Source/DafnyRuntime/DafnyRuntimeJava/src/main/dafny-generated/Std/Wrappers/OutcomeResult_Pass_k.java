// Class OutcomeResult_Pass_k<E>
// Dafny class OutcomeResult_Pass_k<E> compiled into Java
package Std.Wrappers;


@SuppressWarnings({"unchecked", "deprecation"})
public class OutcomeResult_Pass_k<E> extends OutcomeResult<E> {
  public OutcomeResult_Pass_k (dafny.TypeDescriptor<E> _td_E) {
    super(_td_E);
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    OutcomeResult_Pass_k<E> o = (OutcomeResult_Pass_k<E>)other;
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
    s.append("Wrappers.OutcomeResult.Pass'");
    return s.toString();
  }
}
