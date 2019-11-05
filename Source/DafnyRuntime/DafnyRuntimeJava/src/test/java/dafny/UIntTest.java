package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

class UIntTest {

    UInt tenI = new UInt(10);
    short tenUShort = 10;
    UInt tenU = new UInt(tenUShort);
    UInt two = new UInt(2);
    UInt zero = new UInt(0);
    UInt max = new UInt(0xffffffff);

    @Test
    void testComparisons(){
        assertEquals(tenU, tenI);
        assertNotEquals(tenU, max);
        assertEquals(UInt.MAXVALUE, max.value());
        assertEquals(0, zero.value());
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertEquals(0, tenU.compareTo(tenI));
        assertTrue(UInt.compare(tenU, zero) > 0);
        assertTrue(UInt.compare(tenU, max) < 0);
        assertEquals(0, UInt.compare(tenU, tenI));

    }

    @Test
    void testValues(){
        int i = 10;
        long l = 10;
        assertEquals(i, tenU.value());
        assertEquals(l, tenU.longValue());
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    void testArithmetic(){
        assertEquals(10+2, tenU.add(two).value());
        assertEquals(UInt.MAXVALUE, max.add(zero).value());
        assertEquals(8, tenU.subtract(two).value());
        assertEquals(UInt.MAXVALUE-2, max.subtract(two).value());
        assertEquals(20, tenU.multiply(two).value());
        assertEquals(0, max.multiply(zero).value());
        assertEquals(5, tenI.divide(two).value());
        assertEquals(0, zero.divide(max).value());
        assertEquals(0xffffffffL / 10, max.divide(tenI).longValue());
        assertEquals((int)(0xffffffffL / 10), max.divide(tenI).value());
        assertEquals(0, tenU.mod(two).value());
        assertEquals((0xffffffffL)%10, max.mod(tenI).value());
    }

    @Test
    void testFailures(){
        assertThrows(AssertionError.class, () -> new UInt(0x100000000L));
        assertThrows(AssertionError.class, () -> max.divide(zero));
        assertThrows(AssertionError.class, () -> max.mod(zero));
    }
}
