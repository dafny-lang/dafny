// Class Result_Success<R, E>
// Dafny class Result_Success<R, E> compiled into Java
package Std.Wrappers;

import JavaInternal.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Result_Success<R, E> extends Result<R, E> {
  public R _value;
  public Result_Success (dafny.TypeDescriptor<R> _td_R, dafny.TypeDescriptor<E> _td_E, R value) {
    super(_td_R, _td_E);
    this._value = value;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Result_Success<R, E> o = (Result_Success<R, E>)other;
    return true && java.util.Objects.equals(this._value, o._value);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._value);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Wrappers.Result.Success");
    s.append("(");
    s.append(dafny.Helpers.toString(this._value));
    s.append(")");
    return s.toString();
  }
}
