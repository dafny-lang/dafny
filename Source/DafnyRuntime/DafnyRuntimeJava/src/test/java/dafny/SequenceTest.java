package dafny;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import org.junit.jupiter.api.Test;

class SequenceTest {

  int[] testSequenceArr = new int[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7};
  int[] testSequencePreArr = new int[]{1, 3, 2, 4, 2, 4};
  int[] testSequenceNPreArr = new int[]{1, 3, 2, 4, 2, 5};
  int[] testSequenceNPre2Arr = new int[]{1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7, 3};
  int[] testSequenceSubArr = new int[]{2, 4, 6, 5};
  int[] testSequenceTakeArr = new int[]{1, 3, 2, 4, 2};
  int[] testSequenceDropArr = new int[]{4, 6, 5, 4, 1, 7};
  int[] testSequenceEmptyArr = new int[]{};
  DafnySequence<Integer> testSequence = DafnySequence.of(testSequenceArr);
  DafnySequence<Integer> testSequencePre = DafnySequence.of(testSequencePreArr);
  DafnySequence<Integer> testSequenceNPre = DafnySequence.of(testSequenceNPreArr);
  DafnySequence<Integer> testSequenceNPre2 = DafnySequence.of(testSequenceNPre2Arr);
  DafnySequence<Integer> testSequenceSub = DafnySequence.of(testSequenceSubArr);
  DafnySequence<Integer> testSequenceDrop = DafnySequence.of(testSequenceDropArr);
  DafnySequence<Integer> testSequenceTake = DafnySequence.of(testSequenceTakeArr);
  DafnySequence<Integer> testSequenceEmpty = DafnySequence.of(testSequenceEmptyArr);
  DafnySequence<Integer> testCopy = DafnySequence.of(testSequenceArr);
  DafnySequence<Integer> testWrappedSequence = DafnySequence.unsafeWrapRawArray(Type.INT, testSequenceArr);

  @Test
  void testSequencePrefix() {
    assertTrue(testSequencePre.isPrefixOf(testSequence));
    assertFalse(testSequenceNPre.isPrefixOf(testSequence));
    assertFalse(testSequenceNPre2.isPrefixOf(testSequence));
    assertTrue(testSequence.isPrefixOf(testSequence));
    assertFalse(testSequence.isPrefixOf(testSequencePre));
  }

  @Test
  void testSequenceProperPrefix() {
    assertTrue(testSequencePre.isProperPrefixOf(testSequence));
    assertFalse(testSequence.isProperPrefixOf(testSequenceNPre));
    assertFalse(testSequence.isProperPrefixOf(testSequence));
    assertFalse(testSequenceNPre.isProperPrefixOf(testSequence));
    assertFalse(testSequenceNPre2.isProperPrefixOf(testSequence));
  }

  @Test
  void testSequenceConcatenate() {
    DafnySequence<Integer> fatty = testSequence.concatenate(testSequencePre);
    assertEquals(fatty.length(), testSequencePre.length() + testSequence.length());
    for (int i = 0; i < testSequence.length(); i++) {
      assertEquals(fatty.select(i), testSequence.select(i));
    }
    for (int i = 0; i < testSequencePre.length(); i++) {
      assertEquals(fatty.select(i + testSequence.length()), testSequencePre.select(i));
    }
  }

  @Test
  void testSequenceLength() {
    assertEquals(11, testSequence.length());
    assertEquals(6, testSequencePre.length());
    assertEquals(6, testSequenceNPre.length());
    assertEquals(12, testSequenceNPre2.length());
  }

  @Test
  void testSequenceUpdate() {
    DafnySequence<Integer> temp;
    temp = testSequence.update(5, 5);
    DafnySequence<Integer> testUpdate = DafnySequence
        .of(1, 3, 2, 4, 2, 5, 6, 5, 4, 1, 7);
    assertEquals(temp, testUpdate);
    assertEquals(testSequence, testCopy);
  }

  @Test
  void testSequenceMembership() {
    assertTrue(testSequence.contains(1));
    assertTrue(testSequence.contains(2));
    assertTrue(testSequence.contains(3));
    assertTrue(testSequence.contains(4));
    assertTrue(testSequence.contains(5));
    assertTrue(testSequence.contains(6));
    assertTrue(testSequence.contains(7));
    assertFalse(testSequence.contains(8));
    assertFalse(testSequence.contains(9));
    assertFalse(testSequence.contains(10));
  }

  @Test
  void testSequenceSubsequenceStuff() {
    assertEquals(testSequenceSub, testSequence.subsequence(4, 8));
    assertEquals(testSequenceDrop, testSequence.drop(5));
    assertEquals(testSequenceTake, testSequence.take(5));
  }

  @Test
  void testSequenceMultisetConversion() {
    DafnyMultiset<Integer> m = new DafnyMultiset<>();
    m = m.update(1, BigInteger.valueOf(2));
    m = m.update(2, BigInteger.valueOf(2));
    m = m.update(3, BigInteger.valueOf(1));
    m = m.update(4, BigInteger.valueOf(3));
    m = m.update(5, BigInteger.valueOf(1));
    m = m.update(6, BigInteger.valueOf(1));
    m = m.update(7, BigInteger.valueOf(1));
    DafnyMultiset<Integer> c = testSequence.asDafnyMultiset();
    assertEquals(m, c);

  }

  @Test
  void testSequenceSlice() {
    List<Integer> l = new ArrayList<>();
    l.add(5);
    l.add(0);
    l.add(6);
    DafnySequence<DafnySequence<Integer>> sliced = testSequence.slice(l);
    Iterator<DafnySequence<Integer>> it = sliced.iterator();
    assertEquals(it.next(), testSequenceTake);
    assertEquals(it.next(), testSequenceEmpty);
    assertEquals(it.next(), testSequenceDrop);
  }

  @Test
  void testObjectMethods() {
    assertEquals(testSequence, testCopy);
    assertEquals(testSequence.hashCode(), testCopy.hashCode());
    assertEquals("[1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7]", testSequence.toString());
    assertEquals("[1, 3, 2, 4, 2, 4, 6, 5, 4, 1, 7]", testCopy.toString());
  }

  @Test
  @SuppressWarnings("all")
  void testNullFailures() {
    List<Integer> l = null;
    assertThrows(AssertionError.class, () -> DafnySequence.fromList(Type.INT, l));
    assertThrows(AssertionError.class, () -> testSequence.isPrefixOf(null));
    assertThrows(AssertionError.class, () -> testSequence.contains(null));
    assertThrows(AssertionError.class, () -> testSequence.concatenate(null));
    assertThrows(AssertionError.class, () -> testSequence.update(1, null));
    assertThrows(AssertionError.class, () -> testSequence.slice(null));
    assertThrows(AssertionError.class, () -> {
      List<Integer> l1 = new ArrayList<>();
      l1.add(null);
      testSequence.slice(l1);
    });
    assertThrows(NullPointerException.class, () -> testSequence.forEach(null));
  }

  @Test
  void testIndexFailures() {
    assertThrows(AssertionError.class, () -> {
      testSequence.drop(13);
      testSequence.drop(-3);
      testSequence.take(13);
      testSequence.take(-3);
      testSequence.subsequence(-3, 4);
      testSequence.subsequence(3, 42);
      testSequence.subsequence(2, 1);
      testSequence.subsequence(testSequence.length(), testSequence.length());
      testSequence.update(45, 3);
      testSequence.update(-8, 3);
    });
  }

  @Test
  void testNullMembers() {
    Integer[] testNulls = new Integer[]{3, null, 2};
    assertThrows(NullPointerException.class, () -> DafnySequence.of(Type.INT, testNulls));
  }

  @Test
  void testArrayConversion() {
    assertEquals(testSequence, testWrappedSequence);
    int[] convertedArr = (int[]) testSequence.toRawArray();
    assertArrayEquals(convertedArr, testSequenceArr);

    byte[] byteArr = new byte[testSequenceArr.length];
    for (int i = 0; i < testSequenceArr.length; i++) {
      byteArr[i] = (byte) testSequenceArr[i];
    }

    DafnySequence<Byte> testByteSequence = DafnySequence.fromBytes(byteArr);
    DafnySequence<Byte> testWrappedByteSequence = DafnySequence.unsafeWrapBytes(byteArr);
    assertEquals(testByteSequence, testWrappedByteSequence);

    byte[] convertedByteArr = DafnySequence.toByteArray(testByteSequence);
    assertArrayEquals(byteArr, convertedByteArr);
  }
}
