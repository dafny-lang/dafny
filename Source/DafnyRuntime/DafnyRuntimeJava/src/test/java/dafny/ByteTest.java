package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

class ByteTest {

  UByte tenI = new UByte(10);
  byte tenByte = 10;
  UByte tenB = new UByte(tenByte);
  byte negtenByte = -10;
  UByte negtenB = new UByte(negtenByte);
  UByte two = new UByte(2);
  UByte zero = new UByte(0);
  UByte max = new UByte((byte) 0xff);

  @Test
  void testComparisons() {
    assertEquals(tenB, tenI);
    assertNotEquals(tenB, max);
    assertEquals(0xff, max.intValue());
    assertEquals(0, zero.intValue());
    assertTrue(tenB.compareTo(zero) > 0);
    assertTrue(tenB.compareTo(max) < 0);
    assertEquals(0, tenB.compareTo(tenI));
    assertTrue(UByte.compare(tenB, zero) > 0);
    assertTrue(UByte.compare(tenB, max) < 0);
    assertEquals(0, UByte.compare(tenB, tenI));
    assertEquals(new UByte((byte) -1), max);
  }

  @Test
  void testValues() {
    int i = 10;
    long l = 10;
    byte b2 = -1;
    assertEquals(i, tenB.intValue());
    assertEquals(l, tenB.longValue());
    assertEquals(tenByte, tenB.byteValue());
    assertEquals(tenB, new UByte(tenB.byteValue()));
    assertEquals(b2, max.byteValue());
    assertEquals(negtenByte, negtenB.byteValue());
    assertEquals(negtenB, new UByte(negtenB.byteValue()));
    assertEquals(0xff, max.intValue());
    assertEquals(Integer.hashCode(10), tenB.hashCode());
    assertEquals("10", tenB.toString());
  }

  @Test
  void testArithmetic() {
    assertEquals(10 + 2, tenB.add(two).intValue());
    assertEquals(0xff, max.add(zero).intValue());
    assertEquals(8, tenB.subtract(two).intValue());
    assertEquals(0xfd, max.subtract(two).intValue());
    assertEquals(20, tenB.multiply(two).intValue());
    assertEquals(0, max.multiply(zero).intValue());
    assertEquals(5, tenI.divide(two).intValue());
    assertEquals(0, zero.divide(max).intValue());
    assertEquals(0, tenB.mod(two).intValue());
    assertEquals(0xff % 10, max.mod(tenI).intValue());
  }

  @Test
  void testFailures() {
    assertThrows(AssertionError.class, () -> new UByte(0xfff));
    assertThrows(AssertionError.class, () -> max.mod(zero));
  }
}
