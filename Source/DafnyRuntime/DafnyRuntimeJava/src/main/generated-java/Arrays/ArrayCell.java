// Class ArrayCell<T>
// Dafny class ArrayCell<T> compiled into Java
package Arrays;

import Frames_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class ArrayCell<T> {
  public ArrayCell() { }

  public static <T> ArrayCell<T> Default() {
    return Arrays.ArrayCell.create_Unset();
  }
  private static final dafny.TypeDescriptor<ArrayCell> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(ArrayCell.class, () -> Default());
  public static <T> dafny.TypeDescriptor<ArrayCell<T>> _typeDescriptor() {
    return (dafny.TypeDescriptor<ArrayCell<T>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static <T> ArrayCell<T> create_Set(T value) {
    return new ArrayCell_Set<T>(value);
  }
  public static <T> ArrayCell<T> create_Unset() {
    return new ArrayCell_Unset<T>();
  }
  public boolean is_Set() { return this instanceof ArrayCell_Set; }
  public boolean is_Unset() { return this instanceof ArrayCell_Unset; }
  public T dtor_value() {
    ArrayCell<T> d = this;
    return ((ArrayCell_Set<T>)d).value;
  }
}
