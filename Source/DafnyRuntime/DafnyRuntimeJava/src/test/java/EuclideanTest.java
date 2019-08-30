import dafny.DafnyEuclidean;
import org.junit.Test;

import java.math.BigInteger;

import static junit.framework.Assert.assertEquals;

public class EuclideanTest {
    BigInteger two = BigInteger.valueOf(2);

    @Test
    public void testByte() {
        assertEquals(2, DafnyEuclidean.EuclideanDivision((byte) 7, (byte) 3));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision((byte) 7, (byte) -3));
        assertEquals(-3, DafnyEuclidean.EuclideanDivision((byte) -7, (byte) 3));
        assertEquals(3, DafnyEuclidean.EuclideanDivision((byte) -7, (byte) -3));
        assertEquals(Math.floorDiv(0, 1), DafnyEuclidean.EuclideanDivision((byte) 0, (byte) 1));
        assertEquals(Math.floorDiv(2, 1), DafnyEuclidean.EuclideanDivision((byte) 2, (byte) 1));
        assertEquals(Math.floorDiv(13, 2), DafnyEuclidean.EuclideanDivision((byte) 13, (byte) 2));
        assertEquals(Math.floorDiv(-2, 1), DafnyEuclidean.EuclideanDivision((byte) -2, (byte) 1));
        assertEquals(Math.floorDiv(-13, 2), DafnyEuclidean.EuclideanDivision((byte) -13, (byte) 2));
        assertEquals(Math.floorDiv(0, -1), DafnyEuclidean.EuclideanDivision((byte) 0, (byte) -1));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision((byte) 2, (byte) -1));
        assertEquals(-6, DafnyEuclidean.EuclideanDivision((byte) 13, (byte) -2));
        assertEquals(2, DafnyEuclidean.EuclideanDivision((byte) -2, (byte) -1));
        assertEquals(7, DafnyEuclidean.EuclideanDivision((byte) -13, (byte) -2));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision((byte) -14, (byte) 13));
        assertEquals(0, DafnyEuclidean.EuclideanDivision((byte) 14, Byte.MIN_VALUE));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision(Byte.MIN_VALUE, Byte.MAX_VALUE));
        assertEquals(1, DafnyEuclidean.EuclideanDivision(Byte.MIN_VALUE, Byte.MIN_VALUE));
    }

    @Test
    public void testShort() {
        assertEquals(2, DafnyEuclidean.EuclideanDivision((short) 7, (short) 3));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision((short) 7, (short) -3));
        assertEquals(-3, DafnyEuclidean.EuclideanDivision((short) -7, (short) 3));
        assertEquals(3, DafnyEuclidean.EuclideanDivision((short) -7, (short) -3));
        assertEquals(Math.floorDiv(0, 1), DafnyEuclidean.EuclideanDivision((short) 0, (short) 1));
        assertEquals(Math.floorDiv(2, 1), DafnyEuclidean.EuclideanDivision((short) 2, (short) 1));
        assertEquals(Math.floorDiv(13, 2), DafnyEuclidean.EuclideanDivision((short) 13, (short) 2));
        assertEquals(Math.floorDiv(-2, 1), DafnyEuclidean.EuclideanDivision((short) -2, (short) 1));
        assertEquals(Math.floorDiv(-13, 2), DafnyEuclidean.EuclideanDivision((short) -13, (short) 2));
        assertEquals(Math.floorDiv(0, -1), DafnyEuclidean.EuclideanDivision((short) 0, (short) -1));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision((short) 2, (short) -1));
        assertEquals(-6, DafnyEuclidean.EuclideanDivision((short) 13, (short) -2));
        assertEquals(2, DafnyEuclidean.EuclideanDivision((short) -2, (short) -1));
        assertEquals(7, DafnyEuclidean.EuclideanDivision((short) -13, (short) -2));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision((short) -14, (short) 13));
        assertEquals(0, DafnyEuclidean.EuclideanDivision((short) 14, Short.MIN_VALUE));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision(Short.MIN_VALUE, Short.MAX_VALUE));
        assertEquals(1, DafnyEuclidean.EuclideanDivision(Short.MIN_VALUE, Short.MIN_VALUE));
    }

    @Test
    public void testInt() {
        assertEquals(2, DafnyEuclidean.EuclideanDivision(7, 3));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision(7, -3));
        assertEquals(-3, DafnyEuclidean.EuclideanDivision(-7, 3));
        assertEquals(3, DafnyEuclidean.EuclideanDivision(-7, -3));
        assertEquals(Math.floorDiv(0, 1), DafnyEuclidean.EuclideanDivision(0, 1));
        assertEquals(Math.floorDiv(2, 1), DafnyEuclidean.EuclideanDivision(2, 1));
        assertEquals(Math.floorDiv(13, 2), DafnyEuclidean.EuclideanDivision(13, 2));
        assertEquals(Math.floorDiv(-2, 1), DafnyEuclidean.EuclideanDivision(-2, 1));
        assertEquals(Math.floorDiv(-13, 2), DafnyEuclidean.EuclideanDivision(-13, 2));
        assertEquals(Math.floorDiv(0, -1), DafnyEuclidean.EuclideanDivision(0, -1));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision(2, -1));
        assertEquals(-6, DafnyEuclidean.EuclideanDivision(13, -2));
        assertEquals(2, DafnyEuclidean.EuclideanDivision(-2, -1));
        assertEquals(7, DafnyEuclidean.EuclideanDivision(-13, -2));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision(-14, 13));
        assertEquals(0, DafnyEuclidean.EuclideanDivision(14, Integer.MIN_VALUE));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision(Integer.MIN_VALUE, Integer.MAX_VALUE));
        assertEquals(1, DafnyEuclidean.EuclideanDivision(Integer.MIN_VALUE, Integer.MIN_VALUE));
    }

    @Test
    public void testLong() {
        assertEquals(2L, DafnyEuclidean.EuclideanDivision(7, 3));
        assertEquals(-2L, DafnyEuclidean.EuclideanDivision(7, -3));
        assertEquals(-3L, DafnyEuclidean.EuclideanDivision(-7, 3));
        assertEquals(3L, DafnyEuclidean.EuclideanDivision(-7, -3));
        assertEquals(Math.floorDiv(0, 1), DafnyEuclidean.EuclideanDivision(0, 1));
        assertEquals(Math.floorDiv(2, 1), DafnyEuclidean.EuclideanDivision(2, 1));
        assertEquals(Math.floorDiv(13, 2), DafnyEuclidean.EuclideanDivision(13, 2));
        assertEquals(Math.floorDiv(-2, 1), DafnyEuclidean.EuclideanDivision(-2, 1));
        assertEquals(Math.floorDiv(-13, 2), DafnyEuclidean.EuclideanDivision(-13, 2));
        assertEquals(Math.floorDiv(0, -1), DafnyEuclidean.EuclideanDivision(0, -1));
        assertEquals(-2L, DafnyEuclidean.EuclideanDivision(2, -1));
        assertEquals(-6L, DafnyEuclidean.EuclideanDivision(13, -2));
        assertEquals(2L, DafnyEuclidean.EuclideanDivision(-2, -1));
        assertEquals(7L, DafnyEuclidean.EuclideanDivision(-13, -2));
        assertEquals(0L, DafnyEuclidean.EuclideanDivision(14, Long.MIN_VALUE));
        assertEquals(-2L, DafnyEuclidean.EuclideanDivision(Long.MIN_VALUE, Long.MAX_VALUE));
        assertEquals(1L, DafnyEuclidean.EuclideanDivision(Long.MIN_VALUE, Long.MIN_VALUE));
    }

    @Test
    public void testBigInteger() {
        assertEquals(two, DafnyEuclidean.EuclideanDivision(BigInteger.valueOf(7), BigInteger.valueOf(3)));
        assertEquals(two.negate(), DafnyEuclidean.EuclideanDivision(BigInteger.valueOf(7), BigInteger.valueOf(-3)));
        assertEquals(BigInteger.valueOf(-3), DafnyEuclidean.EuclideanDivision(BigInteger.valueOf(-7), BigInteger.valueOf(3)));
        assertEquals(BigInteger.valueOf(3), DafnyEuclidean.EuclideanDivision(BigInteger.valueOf(-7), BigInteger.valueOf(-3)));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanDivision(BigInteger.ZERO, BigInteger.ONE));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanDivision(BigInteger.ZERO, BigInteger.ONE.negate()));
        assertEquals(two, DafnyEuclidean.EuclideanDivision(two, BigInteger.ONE));
        assertEquals(two.negate(), DafnyEuclidean.EuclideanDivision(two.negate(), BigInteger.ONE));
        assertEquals(BigInteger.valueOf(6), DafnyEuclidean.EuclideanDivision(BigInteger.valueOf(13), two));
        assertEquals(BigInteger.valueOf(-7), DafnyEuclidean.EuclideanDivision(BigInteger.valueOf(-13), two));
    }

    @Test
    public void testByteMod() {
        assertEquals(1, DafnyEuclidean.EuclideanModulus((byte) 7, (byte) 3));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((byte) 7, (byte) -3));
        assertEquals(2, DafnyEuclidean.EuclideanModulus((byte) -7, (byte) 3));
        assertEquals(2, DafnyEuclidean.EuclideanModulus((byte) -7, (byte) -3));

        assertEquals(0, DafnyEuclidean.EuclideanModulus((byte) 0, (byte) 1));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((byte) 2, (byte) 1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((byte) 13, (byte) 2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((byte) -2, (byte) 1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((byte) -13, (byte) 2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((byte) 0, (byte) -1));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((byte) 2, (byte) -1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((byte) 13, (byte) -2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((byte) -2, (byte) -1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((byte) -13, (byte) -2));

        assertEquals(14, DafnyEuclidean.EuclideanModulus((byte) 14, Byte.MIN_VALUE));
        assertEquals(12, DafnyEuclidean.EuclideanModulus((byte) -14, (byte) 13));
        assertEquals(Byte.MAX_VALUE - 1, DafnyEuclidean.EuclideanModulus(Byte.MIN_VALUE, Byte.MAX_VALUE));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(Byte.MIN_VALUE, Byte.MIN_VALUE));
    }

    @Test
    public void testShortMod() {
        assertEquals(1, DafnyEuclidean.EuclideanModulus((short) 7, (short) 3));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((short) 7, (short) -3));
        assertEquals(2, DafnyEuclidean.EuclideanModulus((short) -7, (short) 3));
        assertEquals(2, DafnyEuclidean.EuclideanModulus((short) -7, (short) -3));

        assertEquals(0, DafnyEuclidean.EuclideanModulus((short) 0, (short) 1));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((short) 2, (short) 1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((short) 13, (short) 2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((short) -2, (short) 1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((short) -13, (short) 2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((short) 0, (short) -1));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((short) 2, (short) -1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((short) 13, (short) -2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus((short) -2, (short) -1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus((short) -13, (short) -2));

        assertEquals(14, DafnyEuclidean.EuclideanModulus((short) 14, Short.MIN_VALUE));
        assertEquals(12, DafnyEuclidean.EuclideanModulus((short) -14, (short) 13));
        assertEquals(Short.MAX_VALUE - 1, DafnyEuclidean.EuclideanModulus(Short.MIN_VALUE, Short.MAX_VALUE));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(Short.MIN_VALUE, Short.MIN_VALUE));
    }

    @Test
    public void testIntMod() {
        assertEquals(1, DafnyEuclidean.EuclideanModulus(7, 3));
        assertEquals(1, DafnyEuclidean.EuclideanModulus(7, -3));
        assertEquals(2, DafnyEuclidean.EuclideanModulus(-7, 3));
        assertEquals(2, DafnyEuclidean.EuclideanModulus(-7, -3));

        assertEquals(0, DafnyEuclidean.EuclideanModulus(0, 1));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(2, 1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus(13, 2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(-2, 1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus(-13, 2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(0, -1));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(2, -1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus(13, -2));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(-2, -1));
        assertEquals(1, DafnyEuclidean.EuclideanModulus(-13, -2));

        assertEquals(14, DafnyEuclidean.EuclideanModulus(14, Integer.MIN_VALUE));
        assertEquals(12, DafnyEuclidean.EuclideanModulus(-14, 13));
        assertEquals(Integer.MAX_VALUE - 1, DafnyEuclidean.EuclideanModulus(Integer.MIN_VALUE, Integer.MAX_VALUE));
        assertEquals(0, DafnyEuclidean.EuclideanModulus(Integer.MIN_VALUE, Integer.MIN_VALUE));
    }

    @Test
    public void testLongMod() {
        assertEquals(1L, DafnyEuclidean.EuclideanModulus(7, 3));
        assertEquals(1L, DafnyEuclidean.EuclideanModulus(7, -3));
        assertEquals(2L, DafnyEuclidean.EuclideanModulus(-7, 3));
        assertEquals(2L, DafnyEuclidean.EuclideanModulus(-7, -3));

        assertEquals(0L, DafnyEuclidean.EuclideanModulus(0, 1));
        assertEquals(0L, DafnyEuclidean.EuclideanModulus(2, 1));
        assertEquals(1L, DafnyEuclidean.EuclideanModulus(13, 2));
        assertEquals(0L, DafnyEuclidean.EuclideanModulus(-2, 1));
        assertEquals(1L, DafnyEuclidean.EuclideanModulus(-13, 2));
        assertEquals(0L, DafnyEuclidean.EuclideanModulus(0, -1));
        assertEquals(0L, DafnyEuclidean.EuclideanModulus(2, -1));
        assertEquals(1L, DafnyEuclidean.EuclideanModulus(13, -2));
        assertEquals(0L, DafnyEuclidean.EuclideanModulus(-2, -1));
        assertEquals(1L, DafnyEuclidean.EuclideanModulus(-13, -2));

        assertEquals(14L, DafnyEuclidean.EuclideanModulus(14, Long.MIN_VALUE));
        assertEquals(12L, DafnyEuclidean.EuclideanModulus(-14, 13));
        assertEquals(Long.MAX_VALUE - 1, DafnyEuclidean.EuclideanModulus(Long.MIN_VALUE, Long.MAX_VALUE));
        assertEquals(0L, DafnyEuclidean.EuclideanModulus(Long.MIN_VALUE, Long.MIN_VALUE));
    }

    @Test
    public void testBigIntegerMod() {
        assertEquals(BigInteger.ONE, DafnyEuclidean.EuclideanModulus(BigInteger.valueOf(7), BigInteger.valueOf(3)));
        assertEquals(BigInteger.ONE, DafnyEuclidean.EuclideanModulus(BigInteger.valueOf(7), BigInteger.valueOf(-3)));
        assertEquals(two, DafnyEuclidean.EuclideanModulus(BigInteger.valueOf(-7), BigInteger.valueOf(3)));
        assertEquals(two, DafnyEuclidean.EuclideanModulus(BigInteger.valueOf(-7), BigInteger.valueOf(-3)));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanModulus(BigInteger.ZERO, BigInteger.ONE));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanModulus(BigInteger.ZERO, BigInteger.ONE.negate()));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanModulus(two, BigInteger.ONE));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanModulus(two.negate(), BigInteger.ONE));
        assertEquals(BigInteger.ONE, DafnyEuclidean.EuclideanModulus(BigInteger.valueOf(13), two));
        assertEquals(BigInteger.ONE, DafnyEuclidean.EuclideanModulus(BigInteger.valueOf(-13), two));
    }
}
