// Class ArrayCell_Set<T>
// Dafny class ArrayCell_Set<T> compiled into Java
package Arrays;

import Frames_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class ArrayCell_Set<T> extends ArrayCell<T> {
  public T value;
  public ArrayCell_Set (T value) {
    this.value = value;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    ArrayCell_Set<T> o = (ArrayCell_Set<T>)other;
    return true && java.util.Objects.equals(this.value, o.value);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this.value);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Arrays_Compile.ArrayCell.Set");
    s.append("(");
    s.append(dafny.Helpers.toString(this.value));
    s.append(")");
    return s.toString();
  }
}
