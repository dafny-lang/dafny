package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashMap;
import org.junit.jupiter.api.Test;

class MapTest {
    HashMap<Integer, Character> h = new HashMap<>();
    DafnyMap<? extends Integer, ? extends Character> dm = new DafnyMap<>(h);

    @Test
    @SuppressWarnings("unchecked")
    void testSubset(){
        // add map[1 := 'c'] to both h and dm
        h.put(1, 'c');
        dm = DafnyMap.update(dm, 1, 'c');
        assertEquals(dm, new DafnyMap<>(h));
        assertEquals(dm.keySet(), new DafnySet(h.keySet()));
        assertTrue(dm.contains(1));

        // create an updated map, but dm stays the same
        DafnyMap<? extends Integer, ? extends Character> dmUpdated;
        dmUpdated = DafnyMap.<Integer, Character>update(dm, 6, 't');
        assertEquals(dm, new DafnyMap<>(h));

        // remove key 1 from both h and dm
        h.remove(1);
        DafnySet<? extends Integer> ds = DafnySet.of(1);
        dm = DafnyMap.<Integer, Character>subtract(dm, ds);
        assertEquals(dm, new DafnyMap<>(h));

        // remove key 1 from dmUpdated, which gives map[6 := 't']
        dmUpdated = DafnyMap.<Integer, Character>subtract(dmUpdated, ds);
        HashMap<Integer, Character> k = new HashMap<>();
        k.put(6, 't');
        assertEquals(dmUpdated, new DafnyMap<>(k));
    }
}
