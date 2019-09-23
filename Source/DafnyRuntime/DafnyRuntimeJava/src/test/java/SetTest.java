import dafny.DafnySet;
import dafny.DafnyMultiset;
import org.junit.Test;

import java.math.BigInteger;
import java.util.*;

import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;
import static org.hamcrest.CoreMatchers.startsWith;

import org.junit.Rule;
import org.junit.rules.ExpectedException;

public class SetTest {

    DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));
    DafnySet<Integer> testSubSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 8)));
    DafnySet<Integer> testDisjoint = new DafnySet<>(new HashSet<>(Arrays.asList(-1, -2, -6, 10)));
    DafnySet<Integer> testUnion = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8, -1, -2, -6, 10)));
    DafnySet<Integer> testDifference = new DafnySet<>(new HashSet<>(Arrays.asList(6)));
    DafnySet<Integer> testEmpty = new DafnySet<>(new HashSet<>(Arrays.asList()));

    DafnySet<Integer> testCopy = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));

    @Test
    public void testSubset() {
        assertFalse(testSet.isSubsetOf(testSubSet));
        assertTrue(testSubSet.isSubsetOf(testSet));
        assertTrue(testSet.isSubsetOf(testSet));
        assertTrue(testSubSet.isProperSubsetOf(testSet));
        assertFalse(testSet.isProperSubsetOf(testSet));
        assertFalse(testSet.isProperSubsetOf(testSubSet));
    }

    @Test
    public void testContains() {
        assertFalse(testSet.contains(0));
        assertTrue(testSet.contains(6));
        assertFalse(testSubSet.contains(6));
    }

    @Test
    public void testDisjoint() {
        assertFalse(testSet.disjoint(testSubSet));
        assertTrue(testSet.disjoint(testDisjoint));
        assertTrue(testDisjoint.disjoint(testSubSet));
        assertTrue(testDisjoint.disjoint(testSubSet));
    }

    @Test
    public void testUnion() {
        assertEquals(testSet, testSet.union(testSubSet));
        assertEquals(testUnion, testDisjoint.union(testSet));
        assertEquals(testSet, testSubSet.union(testSet));
        assertEquals(testUnion, testSubSet.union(testDisjoint).union(testSet));
    }

    @Test
    public void testDifference() {
        assertEquals(testDifference, testSet.difference(testSubSet));
        assertEquals(testEmpty, testSubSet.difference(testSet));
        assertEquals(testSet, testSet.difference(testDisjoint));
        assertEquals(testDifference, testSet.difference(testDisjoint).difference(testSubSet));
    }

    @Test
    public void testIntersection() {
        assertEquals(testSubSet, testSubSet.intersection(testSet));
        assertEquals(testSubSet, testSubSet.intersection(testSubSet));
        assertEquals(testEmpty, testSubSet.intersection(testDisjoint));
        assertEquals(testEmpty, testSet.intersection(testSubSet).intersection(testDisjoint));
    }

    @Test
    public void testSize() {
        assertEquals(7, testSet.size());
        assertEquals(6, testSubSet.size());
        assertEquals(4, testDisjoint.size());
        assertEquals(11, testUnion.size());
        assertEquals(1, testDifference.size());
        assertEquals(0, testEmpty.size());
    }

    @Test
    public void testSetObjectMethods() {
        assertEquals(testSet, testCopy);
        assertEquals(testSet.hashCode(), testCopy.hashCode());
        assertEquals("{1, 2, 3, 4, 5, 6, 8}", testSet.toString());
        assertEquals("{1, 2, 3, 4, 5, 6, 8}", testCopy.toString());
    }

    @Test
    public void testAllSubsets(){
        DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3)));
        HashSet<DafnySet<Integer>> finalSet = new HashSet<>();
        finalSet.add(new DafnySet<>());
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1, 2)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1, 3)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(2, 3)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(2)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(3)))));
        assertEquals(finalSet, testSet.AllSubsets());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testNullFailures() {
        List<Integer> l = null;
        Set<Integer> s = null;
        thrown.expect(AssertionError.class);
        thrown.expectMessage(startsWith("Precondition Violation"));
        new DafnySet<>(l);
        new DafnySet<>(s);
        testSet.isSubsetOf(null);
        testSet.isProperSubsetOf(null);
        testSet.contains(null);
        testSet.disjoint(null);
        testSet.intersection(null);
        testSet.add(null);
        testSet.union(null);
        testSet.difference(null);
    }

    @Test
    public void testAddRemove() {
        testSet.add(19);
        assertTrue(testSet.contains(19));
        assertFalse(testSet.contains(18));
        testSet.add(18);
        assertTrue(testSet.contains(18));
        Integer[] ele = new Integer[]{1, 3, 18, 19};
        DafnySet<Integer> eles = new DafnySet(Arrays.asList(ele));
        assertTrue(testSet.containsAll(eles));
        testSet.remove(1);
        assertFalse(testSet.containsAll(eles));
        assertFalse(testSet.contains(1));
        testSet.removeAll(eles);
        for(Integer i: ele){
            assertFalse(testSet.contains(i));
        }
        testSet.removeAll(testSet);
        assertTrue(testSet.isEmpty());
    }

    @Test
    public void testConversion(){
        assertEquals(new DafnyMultiset<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)), testSet.asDafnyMultiset());
    }
}
