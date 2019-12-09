package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigInteger;
import org.junit.jupiter.api.Test;

class ULongTest {

    ULong tenI = new ULong(10);
    short tenUShort = 10;
    ULong tenU = new ULong(tenUShort);
    ULong two = new ULong(2);
    ULong zero = new ULong(0);
    ULong max = new ULong(new BigInteger("18446744073709551615"));
    ULong maxMinus1 = new ULong(new BigInteger("18446744073709551614"));
    ULong maxMinus2 = new ULong(new BigInteger("18446744073709551613"));
    ULong large = new ULong(0xfffffffffffffff0L);
    ULong grande = new ULong(0x0ffffffffffffff0L);
    BigInteger MAXBI = new BigInteger("18446744073709551615");  // 0xffff_ffff_ffff_ffff

    @Test
    void testComparisons(){
        assertEquals(tenU, tenI);
        assertNotEquals(tenU, max);
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertEquals(0, tenU.compareTo(tenI));
        assertTrue(ULong.compare(tenU, zero) > 0);
        assertTrue(ULong.compare(tenU, max) < 0);
        assertEquals(0, ULong.compare(tenU, tenI));

    }

    @Test
    void testValues(){
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    void testArithmetic(){
        assertEquals(10+2, tenU.add(two).value());
        assertEquals(0xffffffffffffffffL, max.add(zero).value());
        assertEquals(0xfffffffffffffffeL, maxMinus1.add(zero).value());
        assertEquals(0xfffffffffffffffdL, maxMinus2.add(zero).value());
        assertEquals(0xfffffffffffffffaL, large.add(tenU).value());
        assertEquals(10-2, tenU.subtract(two).value());
        assertEquals(0xffffffffffffffffL - 2, max.subtract(two).value());
        assertEquals(0xffffffffffffffe6L, large.subtract(tenU).value());
        assertEquals(10*2, tenU.multiply(two).value());
        assertEquals(0, max.multiply(zero).value());
        assertEquals(10L * 0x0ffffffffffffff0L, grande.multiply(tenU).value());
        assertEquals(5, tenI.divide(two).value());
        assertEquals(0, zero.divide(max).value());
        assertEquals(1, max.divide(max).value());
        assertEquals(MAXBI.divide(BigInteger.TEN).longValue(), max.divide(tenU).value());
        assertEquals(0, tenU.mod(two).value());
        assertEquals(MAXBI.mod(BigInteger.TEN).longValue(), max.mod(tenI).value());
        assertEquals(tenU.value(), tenU.mod(max).value());
        assertEquals(MAXBI.divide(BigInteger.TEN).longValue(), max.divide(tenI).value());
    }

    @Test
    void testFailures(){
        assertThrows(AssertionError.class, () -> new ULong(MAXBI.add(BigInteger.valueOf(2))));
        assertThrows(AssertionError.class, () -> max.divide(zero));
        assertThrows(AssertionError.class, () -> max.mod(zero));
    }
}
