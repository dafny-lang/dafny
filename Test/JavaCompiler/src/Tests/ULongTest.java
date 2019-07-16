import DafnyClasses.DafnyULong;
import DafnyClasses.DafnyMultiset;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import java.util.*;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class ULongTest {

    DafnyULong tenI = new DafnyULong(10);
    short tenUShort = 10;
    DafnyULong tenU = new DafnyULong(tenUShort);
    DafnyULong two = new DafnyULong(2);
    DafnyULong zero = new DafnyULong(0);
    DafnyULong max = new DafnyULong(new BigInteger("18446744073709551615"));
    DafnyULong large = new DafnyULong(0xfffffffffffffff0l);
    DafnyULong grande = new DafnyULong(0x0ffffffffffffff0l);

    @Test
    public void testComparisons(){
        assertTrue(tenU.equals(tenI));
        assertFalse(tenU.equals(max));
        assertTrue(tenU.compareTo(zero) > 0);
        assertTrue(tenU.compareTo(max) < 0);
        assertTrue(tenU.compareTo(tenI) == 0);
        assertTrue(DafnyULong.compare(tenU, zero) > 0);
        assertTrue(DafnyULong.compare(tenU, max) < 0);
        assertTrue(DafnyULong.compare(tenU, tenI) == 0);

    }

    @Test
    public void testValues(){
        assertEquals(Integer.hashCode(10), tenU.hashCode());
        assertEquals("10", tenU.toString());
    }

    @Test
    public void testArithmetic(){
        assertEquals(10+2, tenU.add(two).value());
        assertEquals(DafnyULong.MAXVALUE, max.add(zero).value());
        assertEquals(0xfffffffffffffffal, large.add(tenU).value());
        assertEquals(10-2, tenU.subtract(two).value());
        assertEquals(DafnyULong.MAXVALUE- 2, max.subtract(two).value());
        assertEquals(0xffffffffffffffe6l, large.subtract(tenU).value());
        assertEquals(10*2, tenU.multiply(two).value());
        assertEquals(0, max.multiply(zero).value());
        assertEquals(10l * 0x0ffffffffffffff0l, grande.multiply(tenU).value());
        assertEquals(5, tenI.divide(two).value());
        assertEquals(0, zero.divide(max).value());
        assertEquals(1, max.divide(max).value());
        assertEquals(DafnyULong.MAXBI.divide(BigInteger.TEN).longValue(), max.divide(tenU).value());
        assertEquals(0, tenU.mod(two).value());
        assertEquals(DafnyULong.MAXBI.mod(BigInteger.TEN).longValue(), max.mod(tenI).value());
        assertEquals(tenU.value(), tenU.mod(max).value());
        assertEquals(DafnyULong.MAXBI.divide(BigInteger.TEN).longValue(), max.divide(tenI).value());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testFailures(){
        thrown.expect(AssertionError.class);
        DafnyULong fail = new DafnyULong(DafnyULong.MAXBI.add(new BigInteger("2")));
        max.add(tenI);
        zero.subtract(two);
        max.multiply(tenU);
        max.divide(zero);
        max.mod(zero);
    }
}
