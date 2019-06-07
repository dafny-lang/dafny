import DafnyClasses.*;
import org.junit.Test;

import javax.swing.tree.TreePath;
import java.awt.event.ItemEvent;
import java.math.BigInteger;
import java.sql.Time;
import java.util.*;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;


public class TupleTest {
    DafnyMultiset<Integer> testMSet = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 2, 4, 3, 5, 7, 3, 2));
    Integer[] testSequenceArr = new Integer[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7};
    DafnySequence<Integer> testSequence = new DafnySequence<>(Arrays.asList(testSequenceArr));
    Character[] testStringArr = new Character[]{'1', '3', '2', '4', '2', '4', '6', '5', '4', '1', '7'};
    DafnyString testString = new DafnyString(Arrays.asList(testStringArr));
    DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));
    Integer integer = 3;
    String string = "Hello";
    StringBuilder sb = new StringBuilder();
    ArrayList<Hashtable<TreeMap<Integer, Time>, ItemEvent>> bigFriend = new ArrayList<>();
    DafnyTuple3<DafnyMultiset<Integer>, DafnySequence<Integer>, DafnyString> dafny = new DafnyTuple3<>(testMSet, testSequence, testString);
    DafnyTuple3<Integer, Integer[], String> types = new DafnyTuple3<>(integer, testSequenceArr, string);
    DafnyTuple3<Integer, Integer[], String> typeCopy = new DafnyTuple3<>(integer, testSequenceArr, string);
    DafnyTuple3<ArrayList, StringBuilder, Integer> complex = new DafnyTuple3<>(bigFriend, sb, integer);

    @Test
    public void testEquals(){
        assertEquals(types, typeCopy);
        assertTrue(types.equals(typeCopy));
        assertFalse(types.equals(complex));
        assertEquals(types.get_0(), complex.get_2());
        assertEquals(dafny.get_0(), testMSet);
        assertEquals(dafny.get_1(), testSequence);
        assertEquals(dafny.get_2(), testString);
    }

    @Test
    public void testHash(){
        assertEquals(types.hashCode(), typeCopy.hashCode());
        assertEquals(types.get_0().hashCode(), complex.get_2().hashCode());
        assertEquals(complex.get_0().hashCode(), new ArrayList().hashCode());
        assertFalse(types.hashCode() == complex.hashCode());
        assertEquals(dafny.get_0().hashCode(), testMSet.hashCode());
        assertEquals(dafny.get_1().hashCode(), testSequence.hashCode());
        assertEquals(dafny.get_2().hashCode(), testString.hashCode());
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
        assertEquals(complex.get_0(), new ArrayList());
        complex.get_0().add(new Hashtable<>());
        assertFalse(complex.get_0().equals(new ArrayList()));
        assertFalse(new StringBuilder().equals(complex.get_1()));
        assertEquals(complex.get_1(), sb);
        sb.append("H");
        assertEquals(complex.get_1(), sb);
        complex.get_1().append("J");
        assertEquals(complex.get_1(), sb);
        assertFalse(new StringBuilder().equals(complex.get_1()));
        assertEquals(complex.get_2(), new Integer(3));
        Integer a = 1 + complex.get_2();
        assertEquals(complex.get_2(), new Integer(3));
        DafnyTuple3<Integer, String, Integer> nullTest = new DafnyTuple3<>(null, null, null);
        assertEquals(nullTest.get_0(), null);
        assertEquals(nullTest.get_1(), null);
        assertEquals(nullTest.get_2(), null);
    }
}
