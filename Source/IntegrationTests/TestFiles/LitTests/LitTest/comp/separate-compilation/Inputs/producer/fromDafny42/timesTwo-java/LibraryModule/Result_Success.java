// Class Result_Success<T, E>
// Dafny class Result_Success<T, E> compiled into Java
package LibraryModule;


@SuppressWarnings({"unchecked", "deprecation"})
public class Result_Success<T, E> extends Result<T, E> {
  public T _value;
  public Result_Success (T value) {
    this._value = value;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Result_Success<T, E> o = (Result_Success<T, E>)other;
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
    s.append("LibraryModule.Result.Success");
    s.append("(");
    s.append(dafny.Helpers.toString(this._value));
    s.append(")");
    return s.toString();
  }
}
