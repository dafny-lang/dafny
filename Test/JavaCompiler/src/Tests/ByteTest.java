import DafnyClasses.DafnyByte;
import DafnyClasses.DafnyMultiset;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import java.util.*;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class ByteTest {

    DafnyByte tenI = new DafnyByte(10);
    byte tenByte = 10;
    DafnyByte tenB = new DafnyByte(tenByte);
    DafnyByte two = new DafnyByte(2);
    DafnyByte zero = new DafnyByte(0);
    DafnyByte max = new DafnyByte((byte)0xff);

    @Test
    public void testComparisons(){
        assertTrue(tenB.equals(tenI));
        assertFalse(tenB.equals(max));
        assertEquals(0xff, max.intValue());
        assertEquals(0, zero.intValue());
        assertTrue(tenB.compareTo(zero) > 0);
        assertTrue(tenB.compareTo(max) < 0);
        assertTrue(tenB.compareTo(tenI) == 0);
        assertTrue(DafnyByte.compare(tenB, zero) > 0);
        assertTrue(DafnyByte.compare(tenB, max) < 0);
        assertTrue(DafnyByte.compare(tenB, tenI) == 0);

    }

    @Test
    public void testValues(){
        float f = 10;
        double d = 10;
        int i = 10;
        long l = 10;
        assertEquals(f, tenB.floatValue());
        assertEquals(d, tenB.doubleValue());
        assertEquals(i, tenB.intValue());
        assertEquals(l, tenB.longValue());
        assertEquals(Integer.hashCode(10), tenB.hashCode());
        assertEquals("10", tenB.toString());
    }

    @Test
    public void testArithmetic(){
        assertEquals(10+2, tenB.add(two).intValue());
        assertEquals(0xff, max.add(zero).intValue());
        assertEquals(8, tenB.subtract(two).intValue());
        assertEquals(0xfd, max.subtract(two).intValue());
        assertEquals(20, tenB.multiply(two).intValue());
        assertEquals(0, max.multiply(zero).intValue());
        assertEquals(5, tenI.divide(two).intValue());
        assertEquals(0, zero.divide(max).intValue());
        assertEquals(0, tenB.mod(two).intValue());
        assertEquals(0xff%10, max.mod(tenI).intValue());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testFailures(){
        thrown.expect(AssertionError.class);
        DafnyByte fail = new DafnyByte(0xfff);
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenB);
        max.divide(zero);
        max.mod(zero);
    }
}
