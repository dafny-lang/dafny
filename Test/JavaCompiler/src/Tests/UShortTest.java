import DafnyClasses.DafnyUShort;
import DafnyClasses.DafnyMultiset;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import java.util.*;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class UShortTest {

    DafnyUShort tenI = new DafnyUShort(10);
    short tenUShort = 10;
    DafnyUShort tenU = new DafnyUShort(tenUShort);
    DafnyUShort two = new DafnyUShort(2);
    DafnyUShort zero = new DafnyUShort(0);
    DafnyUShort max = new DafnyUShort((short)0xffff);

    @Test
    public void testComparisons(){
        assertTrue(tenU.equals(tenI));
        assertFalse(tenU.equals(max));
        assertEquals(0xffff, max.intValue());
        assertEquals(0, zero.intValue());
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertTrue(tenU.compareTo(tenI) == 0);
        assertTrue(DafnyUShort.compare(tenU, zero) > 0);
        assertTrue(DafnyUShort.compare(tenU, max) < 0);
        assertTrue(DafnyUShort.compare(tenU, tenI) == 0);

    }

    @Test
    public void testValues(){
        float f = 10;
        double d = 10;
        int i = 10;
        long l = 10;
        assertEquals(f, tenU.floatValue());
        assertEquals(d, tenU.doubleValue());
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
        assertEquals(0, tenU.modulus(two).intValue());
        assertEquals(0xffff%10, max.modulus(tenI).intValue());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testFailures(){
        thrown.expect(AssertionError.class);
        DafnyUShort fail = new DafnyUShort(0xfffff);
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenU);
        max.divide(zero);
        max.modulus(zero);
    }
}
