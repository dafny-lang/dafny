import dafny.DafnyMultiset;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.math.BigInteger;
import java.util.*;
import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;
import static junit.framework.Assert.assertEquals;
import org.hamcrest.*;


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
    DafnyMultiset<Integer> testCopy = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 2, 4, 3, 5, 7, 3, 2));

    @Test
    public void testSubset(){
        assertFalse(testMSet.isSubsetOf(testMSubSet));
        assertTrue(testMSubSet.isSubsetOf(testMSet));
        assertTrue(testMSet.isSubsetOf(testMSet));
        assertTrue(testMSubSet.isProperSubsetOf(testMSet));
        assertFalse(testMSet.isProperSubsetOf(testMSet));
        assertFalse(testMSet.isProperSubsetOf(testMSubSet));
    }

    @Test
    public void testContains(){
        assertFalse(testMSet.contains(0));
        assertTrue(testMSet.contains(1));
        assertTrue(testMSet.contains(2));
        assertTrue(testMSet.contains(3));
        assertTrue(testMSet.contains(4));
        assertTrue(testMSet.contains(5));
        assertTrue(testMSet.contains(7));
        assertFalse(testMSubSet.contains(7));
    }

    @Test
    public void testDisjoint(){
        assertFalse(testMSet.disjoint(testMSubSet));
        assertTrue(testMSet.disjoint(testMDisjoint));
        assertTrue(testMDisjoint.disjoint(testMSubSet));
        assertTrue(testMDisjoint.disjoint(testMSubSet));
        Map<Integer, BigInteger> testMap = new HashMap<>();
        testMap.put(1, BigInteger.valueOf(7));
        testMap.put(45, BigInteger.valueOf(18));
        testMap.put(-3, BigInteger.ZERO);
        DafnyMultiset<Integer> testZeros= new DafnyMultiset<>(testMap);
        testZeros = testZeros.update(10, BigInteger.ZERO);
        assertTrue(testMDisjoint.disjoint(testZeros));
        assertTrue(testMDisjoint.disjoint(testZeros.intersection(testMSubSet)));
        assertTrue(testMSet.disjoint(testMSet.difference(testMSet)));
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
        assertEquals(BigInteger.valueOf(11), testMSet.cardinality());
        assertEquals(BigInteger.valueOf(9), testMSubSet.cardinality());
        assertEquals(BigInteger.valueOf(7), testMDisjoint.cardinality());
        assertEquals(BigInteger.valueOf(6), testMUnion6.cardinality());
        assertEquals(BigInteger.valueOf(2), testMDifference.cardinality());
        assertEquals(BigInteger.valueOf(0), testMEmpty.cardinality());
    }

    @Test
    public void testMSetObjectMethods(){
        assertEquals(testMSet,testCopy);
        assertEquals(testMSet.hashCode(), testCopy.hashCode());
        assertEquals("multiset{1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 7}",testMSet.toString());
        assertEquals("multiset{1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 7}",testCopy.toString());
    }

    @Test
    public void testUpdate(){
        testMSet = testMSet.update(7, BigInteger.valueOf(3));
        assertEquals(BigInteger.valueOf(3), testMSet.multiplicity(7));
        testMSet = testMSet.update(8, BigInteger.valueOf(5));
        assertEquals(BigInteger.valueOf(5), testMSet.multiplicity(8));
        testMSet = testMSet.update(8, BigInteger.valueOf(0));
        assertFalse(testMSet.contains(8));
    }

    @Test
    public void testConstructors(){
        Set<Integer> s = new HashSet<>();
        s.add(1);
        s.add(2);
        s.add(3);
        Map<Integer, BigInteger> testMap = new HashMap<>();
        testMap.put(1, BigInteger.ONE);
        testMap.put(2, BigInteger.ONE);
        testMap.put(3, BigInteger.ONE);
        DafnyMultiset<Integer> setImp = new DafnyMultiset<>(s);
        DafnyMultiset<Integer> mapImp = new DafnyMultiset<>(testMap);
        assertEquals(setImp, mapImp);
        assertEquals(setImp, testMUnion1);
        assertEquals(mapImp, testMUnion1);
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testNullFailures(){
        List<Integer> l = null;
        Map<Integer, BigInteger> m = null;
        Set<Integer> s = null;
        thrown.expect(AssertionError.class);
        new DafnyMultiset<>(l);
        new DafnyMultiset<>(m);
        new DafnyMultiset<>(s);
        testMSet.isSubsetOf(null);
        testMSet.isProperSubsetOf(null);
        testMSet.disjoint(null);
        testMSet.intersection(null);
        testMSet.update(5, null);
        testMSet.union(null);
        testMSet.difference(null);
    }

    @Test
    public void testNullEntries(){
        testMSet = testMSet.update(null, BigInteger.ONE);
        assertTrue(testMSet.contains(null));
        assertEquals(BigInteger.ONE, testMSet.multiplicity(null));
        testMSet = testMSet.update(null, BigInteger.ZERO);
        assertFalse(testMSet.contains(null));
        assertEquals(BigInteger.ZERO, testMSet.multiplicity(null));
    }

    @Test
    public void testNegativeFailures(){
        Map<Integer, BigInteger> m = new HashMap<>();
        m.put(3, BigInteger.valueOf(-3));
        m.put(2, BigInteger.valueOf(0));
        thrown.expect(AssertionError.class);
        DafnyMultiset<Integer> willFail = new DafnyMultiset<>(m);
        testMSet.update(16, BigInteger.valueOf(-18));
    }

    @Test
    public void testElements(){
        HashMap<Integer, BigInteger> counts = new HashMap<>();
        for(Integer i : testMSet.Elements()){
            if(!counts.containsKey(i)){
                counts.put(i, BigInteger.ONE);
            } else {
                counts.put(i, counts.get(i).add(BigInteger.ONE));
            }
        }
        assertEquals(new DafnyMultiset<Integer>(counts), testMSet);
    }

    @Test
    public void testUniqueElements(){
        for(Integer i : testMSet.UniqueElements()){
            assertTrue(testMSet.contains(i));
        }
    }
}
