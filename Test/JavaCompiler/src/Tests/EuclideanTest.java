import DafnyClasses.DafnyEuclidean;
import org.junit.Test;

import java.math.BigInteger;

import static junit.framework.Assert.assertEquals;

public class EuclideanTest {


    @Test
    public void testInt() {
        assertEquals(2, DafnyEuclidean.EuclideanDivision_int(7, 3));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision_int(7, -3));
        assertEquals(-3, DafnyEuclidean.EuclideanDivision_int(-7, 3));
        assertEquals(3, DafnyEuclidean.EuclideanDivision_int(-7, -3));
        assertEquals(Math.floorDiv(0, 1), DafnyEuclidean.EuclideanDivision_int(0, 1));
        assertEquals(Math.floorDiv(2, 1), DafnyEuclidean.EuclideanDivision_int(2, 1));
        assertEquals(Math.floorDiv(13, 2), DafnyEuclidean.EuclideanDivision_int(13, 2));
        assertEquals(Math.floorDiv(-2, 1), DafnyEuclidean.EuclideanDivision_int(-2, 1));
        assertEquals(Math.floorDiv(-13, 2), DafnyEuclidean.EuclideanDivision_int(-13, 2));
        assertEquals(Math.floorDiv(0, -1), DafnyEuclidean.EuclideanDivision_int(0, -1));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision_int(2, -1));
        assertEquals(-6, DafnyEuclidean.EuclideanDivision_int(13, -2));
        assertEquals(2, DafnyEuclidean.EuclideanDivision_int(-2, -1));
        assertEquals(7, DafnyEuclidean.EuclideanDivision_int(-13, -2));
        assertEquals(0, DafnyEuclidean.EuclideanDivision_int(14, Integer.MIN_VALUE));
        assertEquals(-2, DafnyEuclidean.EuclideanDivision_int(Integer.MIN_VALUE, Integer.MAX_VALUE));
        assertEquals(1, DafnyEuclidean.EuclideanDivision_int(Integer.MIN_VALUE, Integer.MIN_VALUE));
    }

    @Test
    public void testLong() {
        assertEquals(2L, DafnyEuclidean.EuclideanDivision_long(7, 3));
        assertEquals(-2L, DafnyEuclidean.EuclideanDivision_long(7, -3));
        assertEquals(-3L, DafnyEuclidean.EuclideanDivision_long(-7, 3));
        assertEquals(3L, DafnyEuclidean.EuclideanDivision_long(-7, -3));
        assertEquals(Math.floorDiv(0, 1), DafnyEuclidean.EuclideanDivision_long(0, 1));
        assertEquals(Math.floorDiv(2, 1), DafnyEuclidean.EuclideanDivision_long(2, 1));
        assertEquals(Math.floorDiv(13, 2), DafnyEuclidean.EuclideanDivision_long(13, 2));
        assertEquals(Math.floorDiv(-2, 1), DafnyEuclidean.EuclideanDivision_long(-2, 1));
        assertEquals(Math.floorDiv(-13, 2), DafnyEuclidean.EuclideanDivision_long(-13, 2));
        assertEquals(Math.floorDiv(0, -1), DafnyEuclidean.EuclideanDivision_long(0, -1));
        assertEquals(-2L, DafnyEuclidean.EuclideanDivision_long(2, -1));
        assertEquals(-6L, DafnyEuclidean.EuclideanDivision_long(13, -2));
        assertEquals(2L, DafnyEuclidean.EuclideanDivision_long(-2, -1));
        assertEquals(7L, DafnyEuclidean.EuclideanDivision_long(-13, -2));
        assertEquals(0L, DafnyEuclidean.EuclideanDivision_long(14, Long.MIN_VALUE));
        assertEquals(-2L, DafnyEuclidean.EuclideanDivision_long(Long.MIN_VALUE, Long.MAX_VALUE));
        assertEquals(1L, DafnyEuclidean.EuclideanDivision_long(Long.MIN_VALUE, Long.MIN_VALUE));
    }

    @Test
    public void testBigInteger() {
        assertEquals(BigInteger.TWO, DafnyEuclidean.EuclideanDivision(new BigInteger("7"), new BigInteger("3")));
        assertEquals(BigInteger.TWO.negate(), DafnyEuclidean.EuclideanDivision(new BigInteger("7"), new BigInteger("-3")));
        assertEquals(new BigInteger("-3"), DafnyEuclidean.EuclideanDivision(new BigInteger("-7"), new BigInteger("3")));
        assertEquals(new BigInteger("3"), DafnyEuclidean.EuclideanDivision(new BigInteger("-7"), new BigInteger("-3")));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanDivision(BigInteger.ZERO, BigInteger.ONE));
        assertEquals(BigInteger.ZERO, DafnyEuclidean.EuclideanDivision(BigInteger.ZERO, BigInteger.ONE.negate()));
        assertEquals(BigInteger.TWO, DafnyEuclidean.EuclideanDivision(BigInteger.TWO, BigInteger.ONE));
        assertEquals(BigInteger.TWO.negate(), DafnyEuclidean.EuclideanDivision(BigInteger.TWO.negate(), BigInteger.ONE));
        assertEquals(new BigInteger("6"), DafnyEuclidean.EuclideanDivision(new BigInteger("13"), BigInteger.TWO));
        assertEquals(new BigInteger("-7"), DafnyEuclidean.EuclideanDivision(new BigInteger("-13"), BigInteger.TWO));
    }
}
