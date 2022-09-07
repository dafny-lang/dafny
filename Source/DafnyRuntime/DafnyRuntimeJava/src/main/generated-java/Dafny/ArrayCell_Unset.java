// Class ArrayCell_Unset<T>
// Dafny class ArrayCell_Unset<T> compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public class ArrayCell_Unset<T> extends ArrayCell<T> {
  public ArrayCell_Unset () {
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    ArrayCell_Unset<T> o = (ArrayCell_Unset<T>)other;
    return true;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 1;
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny_Compile.ArrayCell.Unset");
    return s.toString();
  }
}
