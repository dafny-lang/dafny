import DafnyClasses.DafnyMultiset;
import DafnyClasses.Dafnymap;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import java.util.*;
import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;
import static org.hamcrest.CoreMatchers.startsWith;


public class MapTest {
    HashMap<Integer, Character> h = new HashMap();
    Dafnymap dm = new Dafnymap(h);

    @Test
    public void testSubset(){
        h.put(1, 'c');
        dm.put(1, 'c');
        assertEquals(dm, new Dafnymap(h));
        assertEquals(dm.entrySet(), h.entrySet());
        assertEquals(dm.keySet(), h.keySet());
        assertTrue(dm.contains(1));
        HashMap<Integer, Character> d = new HashMap<>();
        d.put(6,'l');
        assertTrue(dm.disjoint(new Dafnymap(d)));
        h.remove(1);
        dm.remove(1);
        assertEquals(dm, new Dafnymap(h));
    }
}