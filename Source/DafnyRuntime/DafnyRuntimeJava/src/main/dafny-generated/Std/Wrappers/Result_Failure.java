// Class Result_Failure<R, E>
// Dafny class Result_Failure<R, E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Result_Failure<R, E> extends Result<R, E> {
  public E _error;
  public Result_Failure (dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, E error) {
    super(_td_R, _td_E);
    this._error = error;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Result_Failure<R, E> o = (Result_Failure<R, E>)other;
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
    s.append("Wrappers.Result.Failure");
    s.append("(");
    s.append(dafny.Helpers.toString(this._error));
    s.append(")");
    return s.toString();
  }
}
