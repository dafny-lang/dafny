import dafny.UInt;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class UIntTest {

    UInt tenI = new UInt(10);
    short tenUShort = 10;
    UInt tenU = new UInt(tenUShort);
    UInt two = new UInt(2);
    UInt zero = new UInt(0);
    UInt max = new UInt(0xffffffff);

    @Test
    public void testComparisons(){
        assertTrue(tenU.equals(tenI));
        assertFalse(tenU.equals(max));
        assertEquals(UInt.MAXVALUE, max.value());
        assertEquals(0, zero.value());
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertTrue(tenU.compareTo(tenI) == 0);
        assertTrue(UInt.compare(tenU, zero) > 0);
        assertTrue(UInt.compare(tenU, max) < 0);
        assertTrue(UInt.compare(tenU, tenI) == 0);

    }

    @Test
    public void testValues(){
        float f = 10;
        double d = 10;
        int i = 10;
        long l = 10;
        assertEquals(i, tenU.value());
        assertEquals(l, tenU.longValue());
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    public void testArithmetic(){
        assertEquals(10+2, tenU.add(two).value());
        assertEquals(UInt.MAXVALUE, max.add(zero).value());
        assertEquals(8, tenU.subtract(two).value());
        assertEquals(UInt.MAXVALUE-2, max.subtract(two).value());
        assertEquals(20, tenU.multiply(two).value());
        assertEquals(0, max.multiply(zero).value());
        assertEquals(5, tenI.divide(two).value());
        assertEquals(0, zero.divide(max).value());
        assertEquals(0xffffffffl / 10, max.divide(tenI).longValue());
        assertEquals((int)(0xffffffffl / 10), max.divide(tenI).value());
        assertEquals(0, tenU.mod(two).value());
        assertEquals((0xffffffffl)%10, max.mod(tenI).value());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testFailures(){
        thrown.expect(AssertionError.class);
        UInt fail = new UInt(0x100000000l);
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenU);
        max.divide(zero);
        max.mod(zero);
    }
}
