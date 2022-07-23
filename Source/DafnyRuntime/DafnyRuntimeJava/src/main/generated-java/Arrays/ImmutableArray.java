// Interface ImmutableArray
// Dafny trait ImmutableArray compiled into Java
package Arrays;

import Frames_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public interface ImmutableArray<T> {
  public java.math.BigInteger Length();
  public T At(java.math.BigInteger index);
  public ImmutableArray<T> Slice(java.math.BigInteger start, java.math.BigInteger end);
}
