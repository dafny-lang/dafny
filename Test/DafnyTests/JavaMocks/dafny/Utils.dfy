
   
module Utils {

  class Assertions<T> {
    static method {:extern} assertEquals(expected : T, actual : T)
    requires expected == actual

    static method {:extern} expectEquals(expected : T, actual : T)
    ensures expected == actual

    static method {:extern} assertTrue(condition : bool)
    requires condition

    static method {:extern} expectTrue(condition : bool)
    ensures condition
    
    static method {:extern} assertFalse(condition : bool)
    requires !condition

    static method {:extern} expectFalse(condition : bool)
    ensures !condition
  }

//   public static <T> void assertEquals(dafny.TypeDescriptor<T> typeDescriptor, T left, T right) {
//     org.junit.jupiter.api.Assertions.assertEquals(left, right);
//   }

//   public static <T> void assertTrue(dafny.TypeDescriptor<Boolean> typeDescriptor, Boolean cond) {
//     org.junit.jupiter.api.Assertions.assertTrue(cond);
//   }

//   public static <T> void assertFalse(dafny.TypeDescriptor<Boolean> typeDescriptor, Boolean cond) {
//     org.junit.jupiter.api.Assertions.assertFalse(cond);
//   }

//   class BoundedResponseTestSupport {
//     // Add requires that says the requires on the original method should be violated. 
//     // Do it in the same way as done for assertions.
//     static method {:extern} checkRequires_boundedResponse(lowerBound: int, upperBound: int)
//     requires !(lowerBound >= 0 && lowerBound <= upperBound)
//   }
}