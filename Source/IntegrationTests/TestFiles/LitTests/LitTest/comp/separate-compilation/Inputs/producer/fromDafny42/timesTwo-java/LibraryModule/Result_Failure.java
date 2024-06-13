// Class Result_Failure<T, E>
// Dafny class Result_Failure<T, E> compiled into Java
package LibraryModule;


@SuppressWarnings({"unchecked", "deprecation"})
public class Result_Failure<T, E> extends Result<T, E> {
  public E _error;
  public Result_Failure (E error) {
    this._error = error;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Result_Failure<T, E> o = (Result_Failure<T, E>)other;
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
    s.append("LibraryModule.Result.Failure");
    s.append("(");
    s.append(dafny.Helpers.toString(this._error));
    s.append(")");
    return s.toString();
  }
}
