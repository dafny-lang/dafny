import dafny.ULong;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class ULongTest {

    ULong tenI = new ULong(10);
    short tenUShort = 10;
    ULong tenU = new ULong(tenUShort);
    ULong two = new ULong(2);
    ULong zero = new ULong(0);
    ULong max = new ULong(new BigInteger("18446744073709551615"));
    ULong maxMinus1 = new ULong(new BigInteger("18446744073709551614"));
    ULong maxMinus2 = new ULong(new BigInteger("18446744073709551613"));
    ULong large = new ULong(0xfffffffffffffff0l);
    ULong grande = new ULong(0x0ffffffffffffff0l);
    BigInteger MAXBI = new BigInteger("18446744073709551615");  // 0xffff_ffff_ffff_ffff

    @Test
    public void testComparisons(){
        assertTrue(tenU.equals(tenI));
        assertFalse(tenU.equals(max));
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertTrue(tenU.compareTo(tenI) == 0);
        assertTrue(ULong.compare(tenU, zero) > 0);
        assertTrue(ULong.compare(tenU, max) < 0);
        assertTrue(ULong.compare(tenU, tenI) == 0);

    }

    @Test
    public void testValues(){
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    public void testArithmetic(){
        assertEquals(10+2, tenU.add(two).value());
        assertEquals(0xffffffffffffffffL, max.add(zero).value());
        assertEquals(0xfffffffffffffffeL, maxMinus1.add(zero).value());
        assertEquals(0xfffffffffffffffdL, maxMinus2.add(zero).value());
        assertEquals(0xfffffffffffffffal, large.add(tenU).value());
        assertEquals(10-2, tenU.subtract(two).value());
        assertEquals(0xffffffffffffffffL - 2, max.subtract(two).value());
        assertEquals(0xffffffffffffffe6l, large.subtract(tenU).value());
        assertEquals(10*2, tenU.multiply(two).value());
        assertEquals(0, max.multiply(zero).value());
        assertEquals(10l * 0x0ffffffffffffff0l, grande.multiply(tenU).value());
        assertEquals(5, tenI.divide(two).value());
        assertEquals(0, zero.divide(max).value());
        assertEquals(1, max.divide(max).value());
        assertEquals(MAXBI.divide(BigInteger.TEN).longValue(), max.divide(tenU).value());
        assertEquals(0, tenU.mod(two).value());
        assertEquals(MAXBI.mod(BigInteger.TEN).longValue(), max.mod(tenI).value());
        assertEquals(tenU.value(), tenU.mod(max).value());
        assertEquals(MAXBI.divide(BigInteger.TEN).longValue(), max.divide(tenI).value());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testFailures(){
        thrown.expect(AssertionError.class);
        ULong fail = new ULong(MAXBI.add(BigInteger.valueOf(2)));
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenU);
        max.divide(zero);
        max.mod(zero);
    }
}
