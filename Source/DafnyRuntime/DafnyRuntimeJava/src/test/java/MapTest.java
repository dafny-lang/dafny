import dafny.DafnyMultiset;
import dafny.DafnyMap;
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
    DafnyMap dm = new DafnyMap(h);

    @Test
    public void testSubset(){
        h.put(1, 'c');
        dm.put(1, 'c');
        assertEquals(dm, new DafnyMap(h));
        dm.update(6, 't');
        assertEquals(dm, new DafnyMap(h));
        assertEquals(dm.entrySet(), h.entrySet());
        assertEquals(dm.keySet(), h.keySet());
        assertTrue(dm.contains(1));
        HashMap<Integer, Character> d = new HashMap<>();
        d.put(6,'l');
        assertTrue(dm.disjoint(new DafnyMap(d)));
        h.remove(1);
        dm.remove(1);
        assertEquals(dm, new DafnyMap(h));
    }
}