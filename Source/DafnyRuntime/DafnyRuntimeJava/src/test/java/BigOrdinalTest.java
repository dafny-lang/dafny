import dafny.*;
import org.junit.Test;

import java.math.BigInteger;
import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;

public class BigOrdinalTest {
    @Test
    public void tests(){
        assertFalse(BigOrdinal.IsLimit(BigInteger.ONE));
        assertTrue(BigOrdinal.IsLimit(BigInteger.ZERO));
        assertTrue(BigOrdinal.IsSucc(BigInteger.ONE));
        assertFalse(BigOrdinal.IsSucc(BigInteger.ZERO));
        assertTrue(BigOrdinal.IsNat(BigInteger.ZERO));
        assertEquals(BigInteger.ZERO, BigOrdinal.Offset(BigInteger.ZERO));
    }
}
