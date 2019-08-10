import dafny.BigRational;
import org.junit.Test;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class BigRationalTest {

    BigRational z = new BigRational(0,1);
    BigRational tt = new BigRational(10, 2);
    BigRational ts = new BigRational(3, 7);
    BigRational ntf = new BigRational(-20, 5);

    @Test
    public void testComparisons(){
        assertEquals(z, BigRational.ZERO);
        assertTrue(tt.compareTo(ts) > 0);
        assertTrue(z.compareTo(BigRational.ZERO) == 0);
        assertTrue(ntf.compareTo(ts) < 0);
    }

    @Test
    public void testValues(){
        assertEquals("(10.0 / 2.0)", tt.toString());
    }

    @Test
    public void testArithmetic(){
        assertEquals("(76.0 / 14.0)", tt.add(ts).toString());
        assertEquals("1.0", tt.add(ntf).toString());
        assertEquals("(-3.0 / 7.0)", ts.negate().toString());
        assertEquals("(20.0 / 5.0)", ntf.negate().toString());
        assertEquals("(-64.0 / 14.0)", ts.subtract(tt).toString());
        assertEquals("(155.0 / 35.0)", ts.subtract(ntf).toString());
        assertEquals("(30.0 / 14.0)", ts.multiply(tt).toString());
        assertEquals("(-60.0 / 35.0)", ts.multiply(ntf).toString());
        assertEquals("(6.0 / 70.0)", ts.divide(tt).toString());
        assertEquals("(-15.0 / 140.0)", ts.divide(ntf).toString());
    }
}
