package dafny;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.Test;

class MultisetTest {

  DafnyMultiset<Integer> testMSet = new DafnyMultiset<>(
      Arrays.asList(1, 2, 3, 1, 2, 4, 3, 5, 7, 3, 2));
  DafnyMultiset<Integer> testMSubSet = new DafnyMultiset<>(
      Arrays.asList(1, 2, 1, 2, 4, 3, 5, 3, 2));
  DafnyMultiset<Integer> testMDisjoint = new DafnyMultiset<>(
      Arrays.asList(-1, -3, -1, -5, 10, 11, -4));
  DafnyMultiset<Integer> testMDifference = new DafnyMultiset<>(Arrays.asList(7, 3));
  DafnyMultiset<Integer> testMUnion1 = new DafnyMultiset<>(Arrays.asList(1, 2, 3));
  DafnyMultiset<Integer> testMUnion2 = new DafnyMultiset<>(Arrays.asList(4, 5, 6));
  DafnyMultiset<Integer> testMUnion3 = new DafnyMultiset<>(Arrays.asList(1, 3, 5));
  DafnyMultiset<Integer> testMUnion4 = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 4, 5, 6));
  DafnyMultiset<Integer> testMUnion5 = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 3, 5));
  DafnyMultiset<Integer> testMUnion6 = new DafnyMultiset<>(Arrays.asList(1, 2, 3, 1, 3, 2));
  DafnyMultiset<Integer> testMEmpty = new DafnyMultiset<>(Collections.emptyList());
  DafnyMultiset<Integer> testCopy = new DafnyMultiset<>(
      Arrays.asList(1, 2, 3, 1, 2, 4, 3, 5, 7, 3, 2));

  @Test
  void testSubset() {
    assertFalse(testMSet.isSubsetOf(testMSubSet));
    assertTrue(testMSubSet.isSubsetOf(testMSet));
    assertTrue(testMSet.isSubsetOf(testMSet));
    assertTrue(testMSubSet.isProperSubsetOf(testMSet));
    assertFalse(testMSet.isProperSubsetOf(testMSet));
    assertFalse(testMSet.isProperSubsetOf(testMSubSet));
  }

  @Test
  void testContains() {
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
  void testDisjoint() {
    assertFalse(testMSet.disjoint(testMSubSet));
    assertTrue(testMSet.disjoint(testMDisjoint));
    assertTrue(testMDisjoint.disjoint(testMSubSet));
    assertTrue(testMDisjoint.disjoint(testMSubSet));
    Map<Integer, BigInteger> testMap = new HashMap<>();
    testMap.put(1, BigInteger.valueOf(7));
    testMap.put(45, BigInteger.valueOf(18));
    testMap.put(-3, BigInteger.ZERO);
    DafnyMultiset<Integer> testZeros = new DafnyMultiset<>(testMap);
    testZeros = DafnyMultiset.<Integer>update(testZeros, 10, BigInteger.ZERO);
    assertTrue(testMDisjoint.disjoint(testZeros));
    assertTrue(testMDisjoint.disjoint(DafnyMultiset.<Integer>intersection(testZeros, testMSubSet)));
    assertTrue(testMSet.disjoint(DafnyMultiset.<Integer>difference(testMSet, testMSet)));
  }

  @Test
  void testUnion() {
    assertEquals(testMUnion4, DafnyMultiset.<Integer>union(testMUnion1, testMUnion2));
    assertEquals(testMUnion5, DafnyMultiset.<Integer>union(testMUnion1, testMUnion3));
    assertEquals(testMUnion1, DafnyMultiset.<Integer>union(testMUnion1, testMEmpty));
    assertEquals(testMUnion1, DafnyMultiset.<Integer>union(testMEmpty, testMUnion1));
    assertEquals(testMUnion6, DafnyMultiset.<Integer>union(testMUnion1, testMUnion1));
  }

  @Test
  void testDifference() {
    assertEquals(testMDifference, DafnyMultiset.<Integer>difference(testMSet, testMSubSet));
    assertEquals(testMEmpty, DafnyMultiset.<Integer>difference(testMSubSet, testMSet));
    assertEquals(testMSet, DafnyMultiset.<Integer>difference(testMSet, testMDisjoint));
    assertEquals(testMDifference, DafnyMultiset.<Integer>difference(DafnyMultiset.<Integer>difference(testMSet, testMDisjoint), testMSubSet));
  }

  @Test
  void testIntersection() {
    assertEquals(testMSubSet, DafnyMultiset.<Integer>intersection(testMSubSet, testMSet));
    assertEquals(testMSubSet, DafnyMultiset.<Integer>intersection(testMSubSet, testMSubSet));
    assertEquals(testMEmpty, DafnyMultiset.<Integer>intersection(testMSubSet, testMDisjoint));
    assertEquals(testMEmpty, DafnyMultiset.<Integer>intersection(DafnyMultiset.<Integer>intersection(testMSet, testMSubSet), testMDisjoint));
  }

  @Test
  void testCardinality() {
    assertEquals(BigInteger.valueOf(11), testMSet.cardinality());
    assertEquals(BigInteger.valueOf(9), testMSubSet.cardinality());
    assertEquals(BigInteger.valueOf(7), testMDisjoint.cardinality());
    assertEquals(BigInteger.valueOf(6), testMUnion6.cardinality());
    assertEquals(BigInteger.valueOf(2), testMDifference.cardinality());
    assertEquals(BigInteger.valueOf(0), testMEmpty.cardinality());
  }

  @Test
  void testMSetObjectMethods() {
    assertEquals(testMSet, testCopy);
    assertEquals(testMSet.hashCode(), testCopy.hashCode());
    assertEquals("multiset{1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 7}", testMSet.toString());
    assertEquals("multiset{1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 7}", testCopy.toString());
  }

  @Test
  void testUpdate() {
    testMSet = DafnyMultiset.<Integer>update(testMSet, 7, BigInteger.valueOf(3));
    assertEquals(BigInteger.valueOf(3), DafnyMultiset.<Integer>multiplicity(testMSet, 7));
    testMSet = DafnyMultiset.<Integer>update(testMSet, 8, BigInteger.valueOf(5));
    assertEquals(BigInteger.valueOf(5), DafnyMultiset.<Integer>multiplicity(testMSet, 8));
    testMSet = DafnyMultiset.<Integer>update(testMSet, 8, BigInteger.valueOf(0));
    assertFalse(testMSet.contains(8));
  }

  @Test
  void testConstructors() {
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

  @SuppressWarnings("ConstantConditions")
  @Test
  void testNullFailures() {
    List<Integer> l = null;
    Map<Integer, BigInteger> m = null;
    Set<Integer> s = null;
    assertThrows(AssertionError.class, () -> new DafnyMultiset<>(l));
    assertThrows(AssertionError.class, () -> new DafnyMultiset<>(m));
    assertThrows(AssertionError.class, () -> new DafnyMultiset<>(s));
    assertThrows(AssertionError.class, () -> testMSet.isSubsetOf(null));
    assertThrows(AssertionError.class, () -> testMSet.isProperSubsetOf(null));
    assertThrows(AssertionError.class, () -> testMSet.disjoint(null));
    assertThrows(AssertionError.class, () -> DafnyMultiset.<Integer>intersection(testMSet, null));
    assertThrows(AssertionError.class, () -> DafnyMultiset.<Integer>update(testMSet, 5, null));
    assertThrows(AssertionError.class, () -> DafnyMultiset.<Integer>union(testMSet, null));
    assertThrows(AssertionError.class, () -> DafnyMultiset.<Integer>difference(testMSet, null));
  }

  @Test
  void testNullEntries() {
    testMSet = DafnyMultiset.<Integer>update(testMSet, null, BigInteger.ONE);
    assertTrue(testMSet.contains(null));
    assertEquals(BigInteger.ONE, DafnyMultiset.<Integer>multiplicity(testMSet, null));
    testMSet = DafnyMultiset.<Integer>update(testMSet, null, BigInteger.ZERO);
    assertFalse(testMSet.contains(null));
    assertEquals(BigInteger.ZERO, DafnyMultiset.<Integer>multiplicity(testMSet, null));
  }

  @Test
  void testNegativeFailures() {
    Map<Integer, BigInteger> m = new HashMap<>();
    m.put(3, BigInteger.valueOf(-3));
    m.put(2, BigInteger.valueOf(0));
    assertThrows(AssertionError.class, () -> new DafnyMultiset<>(m));
    assertThrows(AssertionError.class, () -> DafnyMultiset.<Integer>update(testMSet, 16, BigInteger.valueOf(-18)));
  }

  @Test
  void testElements() {
    HashMap<Integer, BigInteger> counts = new HashMap<>();
    for (Integer i : testMSet.Elements()) {
      if (!counts.containsKey(i)) {
        counts.put(i, BigInteger.ONE);
      } else {
        counts.put(i, counts.get(i).add(BigInteger.ONE));
      }
    }
    assertEquals(new DafnyMultiset<>(counts), testMSet);
  }

  @Test
  void testUniqueElements() {
    for (Integer i : testMSet.UniqueElements()) {
      assertTrue(testMSet.contains(i));
    }
  }
}
