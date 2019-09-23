import dafny.*;
import org.junit.Test;

import java.awt.event.ItemEvent;
import java.sql.Time;
import java.util.*;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;


public class TupleTest {
    DafnyMultiset<Integer> testMSet = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 2, 4, 3, 5, 7, 3, 2));
    Integer[] testSequenceArr = new Integer[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7};
    DafnySequence<Integer> testSequence = DafnySequence.fromList(Arrays.asList(testSequenceArr));
    Character[] testStringArr = new Character[]{'1', '3', '2', '4', '2', '4', '6', '5', '4', '1', '7'};
    DafnySequence<Character> testString = DafnySequence.fromList(Arrays.asList(testStringArr));
    DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));
    Integer integer = 3;
    String string = "Hello";
    StringBuilder sb = new StringBuilder();
    ArrayList<Hashtable<TreeMap<Integer, Time>, ItemEvent>> bigFriend = new ArrayList<>();
    Tuple3<DafnyMultiset<Integer>, DafnySequence<Integer>, DafnySequence<Character>> dafny = new Tuple3<>(testMSet, testSequence, testString);
    Tuple3<Integer, Integer[], String> types = new Tuple3<>(integer, testSequenceArr, string);
    Tuple3<Integer, Integer[], String> typeCopy = new Tuple3<>(integer, testSequenceArr, string);
    Tuple3<ArrayList<Hashtable<TreeMap<Integer, Time>, ItemEvent>>, StringBuilder, Integer> complex = new Tuple3<>(bigFriend, sb, integer);

    @Test
    public void testEquals(){
        assertEquals(types, typeCopy);
        assertTrue(types.equals(typeCopy));
        assertFalse(types.equals(complex));
        assertEquals(types.dtor__0(), complex.dtor__2());
        assertEquals(dafny.dtor__0(), testMSet);
        assertEquals(dafny.dtor__1(), testSequence);
        assertEquals(dafny.dtor__2(), testString);
    }

    @Test
    public void testHash(){
        assertEquals(types.hashCode(), typeCopy.hashCode());
        assertEquals(types.dtor__0().hashCode(), complex.dtor__2().hashCode());
        assertEquals(complex.dtor__0().hashCode(), new ArrayList<Object>().hashCode());
        assertFalse(types.hashCode() == complex.hashCode());
        assertEquals(dafny.dtor__0().hashCode(), testMSet.hashCode());
        assertEquals(dafny.dtor__1().hashCode(), testSequence.hashCode());
        assertEquals(dafny.dtor__2().hashCode(), testString.hashCode());
    }

    @Test
    public void testToString(){
        assertEquals(dafny.toString(), "("+testMSet.toString()+", "+testSequence.toString()+", "+testString.toString()+")");
        assertEquals(types.toString(), "("+integer.toString()+", "+testSequenceArr.toString()+", "+string+")");
        assertEquals(typeCopy.toString(), "("+integer.toString()+", "+testSequenceArr.toString()+", "+string+")");
        assertEquals(complex.toString(), "("+bigFriend.toString()+", "+sb.toString()+", "+integer.toString()+")");
    }

    @Test
    public void testGet(){
        assertEquals(complex.dtor__0(), new ArrayList<>());
        complex.dtor__0().add(new Hashtable<>());
        assertFalse(complex.dtor__0().equals(new ArrayList<>()));
        assertFalse(new StringBuilder().equals(complex.dtor__1()));
        assertEquals(complex.dtor__1(), sb);
        sb.append("H");
        assertEquals(complex.dtor__1(), sb);
        complex.dtor__1().append("J");
        assertEquals(complex.dtor__1(), sb);
        assertFalse(new StringBuilder().equals(complex.dtor__1()));
        assertEquals(complex.dtor__2(), new Integer(3));
        @SuppressWarnings("unused")
        Integer a = 1 + complex.dtor__2();
        assertEquals(complex.dtor__2(), new Integer(3));
        Tuple3<Integer, String, Integer> nullTest = new Tuple3<>(null, null, null);
        assertEquals(nullTest.dtor__0(), null);
        assertEquals(nullTest.dtor__1(), null);
        assertEquals(nullTest.dtor__2(), null);
    }
}
