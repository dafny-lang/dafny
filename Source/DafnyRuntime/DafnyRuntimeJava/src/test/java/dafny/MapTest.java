package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashMap;
import org.junit.jupiter.api.Test;

class MapTest {
    HashMap<Integer, Character> h = new HashMap<>();
    DafnyMap<Integer, Character> dm = new DafnyMap<>(h);

    @Test
    void testSubset(){
        h.put(1, 'c');
        dm.put(1, 'c');
        assertEquals(dm, new DafnyMap<>(h));
        dm.update(6, 't');
        assertEquals(dm, new DafnyMap<>(h));
        assertEquals(dm.entrySet(), h.entrySet());
        assertEquals(dm.keySet(), h.keySet());
        assertTrue(dm.contains(1));
        HashMap<Integer, Character> d = new HashMap<>();
        d.put(6,'l');
        h.remove(1);
        dm.remove(1);
        assertEquals(dm, new DafnyMap<>(h));
    }
}
