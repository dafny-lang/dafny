package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.junit.jupiter.api.Test;

class SetTest {

    DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));
    DafnySet<Integer> testSubSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 8)));
    DafnySet<Integer> testDisjoint = new DafnySet<>(new HashSet<>(Arrays.asList(-1, -2, -6, 10)));
    DafnySet<Integer> testUnion = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8, -1, -2, -6, 10)));
    DafnySet<Integer> testDifference = new DafnySet<>(new HashSet<>(Collections.singletonList(6)));
    DafnySet<Integer> testEmpty = new DafnySet<>(new HashSet<>(Collections.emptyList()));

    DafnySet<Integer> testCopy = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));

    @Test
    void testSubset() {
        assertFalse(testSet.isSubsetOf(testSubSet));
        assertTrue(testSubSet.isSubsetOf(testSet));
        assertTrue(testSet.isSubsetOf(testSet));
        assertTrue(testSubSet.isProperSubsetOf(testSet));
        assertFalse(testSet.isProperSubsetOf(testSet));
        assertFalse(testSet.isProperSubsetOf(testSubSet));
    }

    @Test
    void testContains() {
        assertFalse(testSet.contains(0));
        assertTrue(testSet.contains(6));
        assertFalse(testSubSet.contains(6));
    }

    @Test
    void testDisjoint() {
        assertFalse(testSet.disjoint(testSubSet));
        assertTrue(testSet.disjoint(testDisjoint));
        assertTrue(testDisjoint.disjoint(testSubSet));
        assertTrue(testDisjoint.disjoint(testSubSet));
    }

    @Test
    void testUnion() {
        assertEquals(testSet, DafnySet.<Integer>union(testSet, testSubSet));
        assertEquals(testUnion, DafnySet.<Integer>union(testDisjoint, testSet));
        assertEquals(testSet, DafnySet.<Integer>union(testSubSet, testSet));
        assertEquals(testUnion, DafnySet.<Integer>union(DafnySet.<Integer>union(testSubSet, testDisjoint), testSet));
    }

    @Test
    void testDifference() {
        assertEquals(testDifference, DafnySet.<Integer>difference(testSet, testSubSet));
        assertEquals(testEmpty, DafnySet.<Integer>difference(testSubSet, testSet));
        assertEquals(testSet, DafnySet.<Integer>difference(testSet, testDisjoint));
        assertEquals(testDifference, DafnySet.<Integer>difference(DafnySet.<Integer>difference(testSet, testDisjoint), testSubSet));
    }

    @Test
    void testIntersection() {
        assertEquals(testSubSet, DafnySet.<Integer>intersection(testSubSet, testSet));
        assertEquals(testSubSet, DafnySet.<Integer>intersection(testSubSet, testSubSet));
        assertEquals(testEmpty, DafnySet.<Integer>intersection(testSubSet, testDisjoint));
        assertEquals(testEmpty, DafnySet.<Integer>intersection(DafnySet.<Integer>intersection(testSet, testSubSet), testDisjoint));
    }

    @Test
    void testSize() {
        assertEquals(7, testSet.size());
        assertEquals(6, testSubSet.size());
        assertEquals(4, testDisjoint.size());
        assertEquals(11, testUnion.size());
        assertEquals(1, testDifference.size());
        assertEquals(0, testEmpty.size());
    }

    @Test
    void testSetObjectMethods() {
        assertEquals(testSet, testCopy);
        assertEquals(testSet.hashCode(), testCopy.hashCode());
        assertEquals("{1, 2, 3, 4, 5, 6, 8}", testSet.toString());
        assertEquals("{1, 2, 3, 4, 5, 6, 8}", testCopy.toString());
    }

    @Test
    void testAllSubsets(){
        DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3)));
        HashSet<DafnySet<Integer>> finalSet = new HashSet<>();
        finalSet.add(new DafnySet<>());
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1, 2)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(1, 3)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Arrays.asList(2, 3)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Collections.singletonList(1)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Collections.singletonList(2)))));
        finalSet.add(new DafnySet<>(new DafnySet<>(new HashSet<>(Collections.singletonList(3)))));
        assertEquals(finalSet, testSet.AllSubsets());
    }

    @Test
    void testNullFailures() {
        List<Integer> l = null;
        Set<Integer> s = null;
        assertThrows(AssertionError.class, () -> new DafnySet<>(l));
        assertThrows(AssertionError.class, () -> new DafnySet<>(s));
        assertThrows(AssertionError.class, () -> testSet.isSubsetOf(null));
        assertThrows(AssertionError.class, () -> testSet.isProperSubsetOf(null));
        assertThrows(AssertionError.class, () -> testSet.contains(null));
        assertThrows(AssertionError.class, () -> testSet.disjoint(null));
        assertThrows(AssertionError.class, () -> DafnySet.<Integer>intersection(testSet, null));
        assertThrows(AssertionError.class, () -> testSet.add(null));
        assertThrows(AssertionError.class, () -> DafnySet.<Integer>union(testSet, null));
        assertThrows(AssertionError.class, () -> DafnySet.<Integer>difference(testSet, null));
    }

    @Test
    @SuppressWarnings("unchecked")
    void testAddRemove() {
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
    void testConversion(){
        assertEquals(new DafnyMultiset<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)), testSet.asDafnyMultiset());
    }
}
