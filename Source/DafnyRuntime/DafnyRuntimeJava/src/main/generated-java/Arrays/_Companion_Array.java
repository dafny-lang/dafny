// Interface Array
// Dafny trait Array compiled into Java
package Arrays;

import Frames_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class _Companion_Array<T> {
  public _Companion_Array() {
  }
  public static <T> dafny.TypeDescriptor<Array<T>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T) {
    return (dafny.TypeDescriptor<Array<T>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.referenceWithInitializer(Array.class, () -> null);
  }
}
