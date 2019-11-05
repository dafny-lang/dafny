package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

class UShortTest {

    UShort tenI = new UShort(10);
    short tenUShort = 10;
    UShort tenU = new UShort(tenUShort);
    UShort two = new UShort(2);
    UShort zero = new UShort(0);
    UShort max = new UShort((short)0xffff);

    @Test
    void testComparisons(){
        assertEquals(tenU, tenI);
        assertNotEquals(tenU, max);
        assertEquals(0xffff, max.intValue());
        assertEquals(0, zero.intValue());
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertEquals(0, tenU.compareTo(tenI));
        assertTrue(UShort.compare(tenU, zero) > 0);
        assertTrue(UShort.compare(tenU, max) < 0);
        assertEquals(0, UShort.compare(tenU, tenI));

    }

    @Test
    void testValues(){
        int i = 10;
        long l = 10;
        assertEquals(i, tenU.intValue());
        assertEquals(l, tenU.longValue());
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    void testArithmetic(){
        assertEquals(10+2, tenU.add(two).intValue());
        assertEquals(0xffff, max.add(zero).intValue());
        assertEquals(8, tenU.subtract(two).intValue());
        assertEquals(0xfffd, max.subtract(two).intValue());
        assertEquals(20, tenU.multiply(two).intValue());
        assertEquals(0, max.multiply(zero).intValue());
        assertEquals(5, tenI.divide(two).intValue());
        assertEquals(0, zero.divide(max).intValue());
        assertEquals(0, tenU.mod(two).intValue());
        assertEquals(0xffff%10, max.mod(tenI).intValue());
    }

    @Test
    void testFailures() {
        assertThrows(AssertionError.class, () -> new UShort(0xfffff));
        assertThrows(AssertionError.class, () -> max.divide(zero));
        assertThrows(AssertionError.class, () -> max.mod(zero));
    }
}
