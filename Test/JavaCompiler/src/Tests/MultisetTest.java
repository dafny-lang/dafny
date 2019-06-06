package Tests;

import DafnyClasses.DafnyMultiset;
import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;


public class MultisetTest {

    DafnyMultiset<Integer> testMSet = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 2, 4, 3, 5, 7, 3, 2));
    DafnyMultiset<Integer> testMSubSet = new DafnyMultiset<>(Arrays.asList(1, 2, 1, 2, 4, 3, 5, 3, 2));
    DafnyMultiset<Integer> testMDisjoint = new DafnyMultiset<>(Arrays.asList(-1, -3, -1, -5, 10, 11, -4));
    DafnyMultiset<Integer> testMDifference = new DafnyMultiset<>(Arrays.asList(7, 3));
    DafnyMultiset<Integer> testMUnion1 = new DafnyMultiset<>(Arrays.asList(1, 2, 3));
    DafnyMultiset<Integer> testMUnion2 = new DafnyMultiset<>(Arrays.asList(4, 5, 6));
    DafnyMultiset<Integer> testMUnion3 = new DafnyMultiset<>(Arrays.asList(1, 3, 5));
    DafnyMultiset<Integer> testMUnion4 = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 4, 5, 6));
    DafnyMultiset<Integer> testMUnion5 = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 3, 5));
    DafnyMultiset<Integer> testMUnion6 = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 3, 2));
    DafnyMultiset<Integer> testMEmpty = new DafnyMultiset<>(Arrays.asList());

    @Test
    public void testSubset(){
        assertTrue(testMSet.isSubset(testMSubSet));
        assertFalse(testMSubSet.isSubset(testMSet));
        assertTrue(testMSet.isSubset(testMSet));
        assertTrue(testMSet.isProperSubset(testMSubSet));
        assertFalse(testMSet.isProperSubset(testMSet));
        assertFalse(testMSubSet.isProperSubset(testMSet));
    }

    @Test
    public void testContains(){
        assertFalse(testMSet.contains(0));
        assertTrue(testMSet.contains(2));
        assertFalse(testMSubSet.contains(7));
    }

    @Test
    public void testDisjoint(){
        assertFalse(testMSet.disjoint(testMSubSet));
        assertTrue(testMSet.disjoint(testMDisjoint));
        assertTrue(testMDisjoint.disjoint(testMSubSet));
        assertTrue(testMDisjoint.disjoint(testMSubSet));
    }

    @Test
    public void testUnion(){
        assertEquals(testMUnion4, testMUnion1.union(testMUnion2));
        assertEquals(testMUnion5, testMUnion1.union(testMUnion3));
        assertEquals(testMUnion1, testMUnion1.union(testMEmpty));
        assertEquals(testMUnion1, testMEmpty.union(testMUnion1));
        assertEquals(testMUnion6, testMUnion1.union(testMUnion1));
    }

    @Test
    public void testDifference(){
        assertEquals(testMDifference, testMSet.difference(testMSubSet));
        assertEquals(testMEmpty, testMSubSet.difference(testMSet));
        assertEquals(testMSet, testMSet.difference(testMDisjoint));
        assertEquals(testMDifference, testMSet.difference(testMDisjoint).difference(testMSubSet));
    }

    @Test
    public void testIntersection(){
        assertEquals(testMSubSet, testMSubSet.intersection(testMSet));
        assertEquals(testMSubSet, testMSubSet.intersection(testMSubSet));
        assertEquals(testMEmpty, testMSubSet.intersection(testMDisjoint));
        assertEquals(testMEmpty, testMSet.intersection(testMSubSet).intersection(testMDisjoint));
    }

    @Test
    public void testCardinality(){
        assertEquals(new BigInteger("11"), testMSet.cardinality());
        assertEquals(new BigInteger("9"), testMSubSet.cardinality());
        assertEquals(new BigInteger("7"), testMDisjoint.cardinality());
        assertEquals(new BigInteger("6"), testMUnion6.cardinality());
        assertEquals(new BigInteger("2"), testMDifference.cardinality());
        assertEquals(new BigInteger("0"), testMEmpty.cardinality());
    }

    @Test
    public void testUpdate(){
        testMSet.update(7, new BigInteger("3"));
        assertEquals(new BigInteger("3"), testMSet.multiplicity(7));
        testMSet.update(8, new BigInteger("5"));
        assertEquals(new BigInteger("5"), testMSet.multiplicity(8));
        testMSet.update(8, new BigInteger("0"));
        assertFalse(testMSet.contains(8));
    }
}