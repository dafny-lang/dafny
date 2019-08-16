import dafny.UShort;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class UShortTest {

    UShort tenI = new UShort(10);
    short tenUShort = 10;
    UShort tenU = new UShort(tenUShort);
    UShort two = new UShort(2);
    UShort zero = new UShort(0);
    UShort max = new UShort((short)0xffff);

    @Test
    public void testComparisons(){
        assertTrue(tenU.equals(tenI));
        assertFalse(tenU.equals(max));
        assertEquals(0xffff, max.intValue());
        assertEquals(0, zero.intValue());
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertTrue(tenU.compareTo(tenI) == 0);
        assertTrue(UShort.compare(tenU, zero) > 0);
        assertTrue(UShort.compare(tenU, max) < 0);
        assertTrue(UShort.compare(tenU, tenI) == 0);

    }

    @Test
    public void testValues(){
        float f = 10;
        double d = 10;
        int i = 10;
        long l = 10;
        assertEquals(i, tenU.intValue());
        assertEquals(l, tenU.longValue());
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    public void testArithmetic(){
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

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testFailures(){
        thrown.expect(AssertionError.class);
        UShort fail = new UShort(0xfffff);
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenU);
        max.divide(zero);
        max.mod(zero);
    }
}
