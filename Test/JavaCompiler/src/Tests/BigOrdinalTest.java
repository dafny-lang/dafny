import DafnyClasses.DafnyBigOrdinal;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class BigOrdinalTest {
    @Test
    public void tests(){
        assertFalse(DafnyBigOrdinal.IsLimit(BigInteger.ONE));
        assertTrue(DafnyBigOrdinal.IsLimit(BigInteger.ZERO));
        assertTrue(DafnyBigOrdinal.IsSucc(BigInteger.ONE));
        assertFalse(DafnyBigOrdinal.IsSucc(BigInteger.ZERO));
        assertTrue(DafnyBigOrdinal.IsNat(BigInteger.ZERO));
        assertEquals(BigInteger.ZERO, DafnyBigOrdinal.Offset(BigInteger.ZERO));
    }
}
