package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigInteger;
import org.junit.jupiter.api.Test;

class BigOrdinalTest {

  @Test
  void tests() {
    assertFalse(BigOrdinal.IsLimit(BigInteger.ONE));
    assertTrue(BigOrdinal.IsLimit(BigInteger.ZERO));
    assertTrue(BigOrdinal.IsSucc(BigInteger.ONE));
    assertFalse(BigOrdinal.IsSucc(BigInteger.ZERO));
    assertTrue(BigOrdinal.IsNat(BigInteger.ZERO));
    assertEquals(BigInteger.ZERO, BigOrdinal.Offset(BigInteger.ZERO));
  }
}
