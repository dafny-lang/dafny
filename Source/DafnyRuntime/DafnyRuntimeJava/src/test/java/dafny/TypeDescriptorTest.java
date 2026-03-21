package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

class TypeDescriptorTest {

  @Test
  void newArrayForReferenceTypeReturnsObjectArray() {
    TypeDescriptor<String> type = TypeDescriptor.reference(String.class);
    Object arr = type.newArray(5);
    assertTrue(arr instanceof Object[]);
    assertEquals(5, ((Object[]) arr).length);
  }

  @Test
  void newArrayForPrimitiveTypeReturnsTypedArray() {
    Object arr = TypeDescriptor.INT.newArray(5);
    assertTrue(arr instanceof int[]);
    assertEquals(5, ((int[]) arr).length);
  }
}
