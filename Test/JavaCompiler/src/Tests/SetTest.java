package Tests;

import DafnyClasses.DafnySet;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.HashSet;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class SetTest {

    DafnySet<Integer> testSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8)));
    DafnySet<Integer> testSubSet = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 8)));
    DafnySet<Integer> testDisjoint = new DafnySet<>(new HashSet<>(Arrays.asList(-1, -2, -6, 10)));
    DafnySet<Integer> testUnion = new DafnySet<>(new HashSet<>(Arrays.asList(1, 2, 3, 4, 5, 6, 8,-1, -2, -6, 10)));
    DafnySet<Integer> testDifference = new DafnySet<>(new HashSet<>(Arrays.asList(6)));
    DafnySet<Integer> testEmpty= new DafnySet<>(new HashSet<>(Arrays.asList()));

    @Test
    public void testSubset(){
        assertTrue(testSet.isSubset(testSubSet));
        assertFalse(testSubSet.isSubset(testSet));
        assertTrue(testSet.isSubset(testSet));
        assertTrue(testSet.isProperSubset(testSubSet));
        assertFalse(testSet.isProperSubset(testSet));
        assertFalse(testSubSet.isProperSubset(testSet));
    }

    @Test
    public void testContains(){
        assertFalse(testSet.contains(0));
        assertTrue(testSet.contains(6));
        assertFalse(testSubSet.contains(6));
        assertTrue(testSet.getInnerSet().containsAll(Arrays.asList(1,3, 5, 8)));
        assertFalse(testSet.getInnerSet().containsAll(Arrays.asList(1,2,3,7)));
        assertFalse(testSubSet.getInnerSet().containsAll(Arrays.asList(1,3,6)));
    }

    @Test
    public void testDisjoint(){
        assertFalse(testSet.disjoint(testSubSet));
        assertTrue(testSet.disjoint(testDisjoint));
        assertTrue(testDisjoint.disjoint(testSubSet));
        assertTrue(testDisjoint.disjoint(testSubSet));
    }

    @Test
    public void testUnion(){
        assertEquals(testSet, testSet.union(testSubSet));
        assertEquals(testUnion, testDisjoint.union(testSet));
        assertEquals(testSet, testSubSet.union(testSet));
        assertEquals(testUnion, testSubSet.union(testDisjoint).union(testSet));
    }

    @Test
    public void testDifference(){
        assertEquals(testDifference, testSet.difference(testSubSet));
        assertEquals(testEmpty, testSubSet.difference(testSet));
        assertEquals(testSet, testSet.difference(testDisjoint));
        assertEquals(testDifference, testSet.difference(testDisjoint).difference(testSubSet));
    }

    @Test
    public void testIntersection(){
        assertEquals(testSubSet, testSubSet.intersection(testSet));
        assertEquals(testSubSet, testSubSet.intersection(testSubSet));
        assertEquals(testEmpty, testSubSet.intersection(testDisjoint));
        assertEquals(testEmpty, testSet.intersection(testSubSet).intersection(testDisjoint));
    }

    @Test
    public void testSize(){
        assertEquals(7, testSet.size());
        assertEquals(6, testSubSet.size());
        assertEquals(4, testDisjoint.size());
        assertEquals(11, testUnion.size());
        assertEquals(1, testDifference.size());
        assertEquals(0, testEmpty.size());
    }
}