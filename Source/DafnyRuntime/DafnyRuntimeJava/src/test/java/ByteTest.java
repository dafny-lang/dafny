import dafny.UByte;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class ByteTest {

    UByte tenI = new UByte(10);
    byte tenByte = 10;
    UByte tenB = new UByte(tenByte);
    byte negtenByte = -10;
    UByte negtenB = new UByte(negtenByte);
    UByte two = new UByte(2);
    UByte zero = new UByte(0);
    UByte max = new UByte((byte)0xff);

    @Test
    public void testComparisons(){
        assertTrue(tenB.equals(tenI));
        assertFalse(tenB.equals(max));
        assertEquals(0xff, max.intValue());
        assertEquals(0, zero.intValue());
        assertTrue(tenB.compareTo(zero) > 0);
        assertTrue(tenB.compareTo(max) < 0);
        assertTrue(tenB.compareTo(tenI) == 0);
        assertTrue(UByte.compare(tenB, zero) > 0);
        assertTrue(UByte.compare(tenB, max) < 0);
        assertTrue(UByte.compare(tenB, tenI) == 0);
        assertEquals(new UByte((byte)-1), max);
    }

    @Test
    public void testValues(){
        float f = 10;
        double d = 10;
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
        UByte fail = new UByte(0xfff);
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenB);
        max.divide(zero);
        max.mod(zero);
    }
}
