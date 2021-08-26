# Test Generation for Dafny

[**Purpose**](#purpose) <br>
[**General Approach**](#general-approach) <br>
[**Implementation**](#implementation) <br>
[**How to Generate Tests?**](#how-to-generate-tests) <br>
[**How to Run Tests?**](#how-to-run-tests) <br>
[**Example**](#example)

## Purpose

Block- and path-coverage tests of Dafny code can be used to:
- Identify dead code
- Test the use and specification of external methods
- Check that code is efficient
- Test new and existing compilers of Dafny to other languages

## General Approach

To generate a test that covers a particular basic block or path, we add an
assertion to the target method that is violated in the event that a particular
block is visited or a particular path is taken. We then use the counterexample
model provided by the prover to extract the inputs to the target method that
cause the assertion violation, which gives us the desired test case.

While these manipulations could be done with the Dafny source directly, we
instead modify the Boogie translation, since it is much easier to work
with basic blocks and paths on this lower level.

Objects present an obstacle for test generation since it is not possible to
mock objects in Dafny and the prover model does not specify how an object was
allocated\constructed. Currently, we require that a test method take any
object it needs as an argument. This allows us to compile the test methods
to Java or another language where object mocking is possible (see
[How to Run Tests?](#how-to-run-tests)).

Even though it is possible to run the tests in this way, we currently provide
no oracle against which to compare the result. In the future, it may be
possible to generate an oracle directly from the prover model provided that
there is no non-determinism in the tested code.


## Implementation

- [Main.cs](Main.cs) - contains the two methods that should be used to query
  Dafny to generate tests.
- [Utils.cs](Utils.cs) - a small collection of utility methods used elsewhere
  in the project.
- [TestMethod.cs](TestMethod.cs) - generates a test that calls the target
  method with arguments triggering an assertion violation described by Z3's
  counterexample model. This is where all the interaction with DafnyServer's
  counterexample extraction code takes place.
- [ProgramModification.cs](ProgramModification.cs) - represents a modification
  of the original Boogie program (which is in turn generated in `Main.cs` by
  translating Dafny input to Boogie). Can be verified and, if verification
  fails, one can pass the counterexample log as constructor
  argument to `TestMethod`.
- [ProgramModifier.cs](ProgramModifier.cs) - an abstract class that contains
  utilities for annotating Boogie Programs, inlining Dafny methods after they
  are translated to Boogie, etc. This is all necessary for generating
  instances of `ProgramModification`
- [BlockBasedModifier.cs](BlockBasedModifier.cs) and
  [PathBasedModifier.cs](PathBasedModifier.cs) - subclasses of
  `ProgramModifier` that generate instances of `ProgramModification` by
  inserting assertions that fail when a particular block is visited or a
  particular path is taken, respectively.
- [DafnyInfo.cs](DafnyInfo.cs) - takes a Dafny Program and extracts certain
  information about it that is then used in `TestMethod.cs` and `Main.cs`

## How to Generate Tests?

- Test generation currently works with all basic types, user-defined classes,
  sequences, sets, and maps. It does not work with datatypes, arrays, and
  multisets
- To generate block- or path-coverage tests use the `/testMode:Block` or
  `/testMode:Path` arguments respectively. You will likely also need
  `definiteAssignment:3`, which will endure that you generate tests even for those
  methods that do not contain any assertions or pre-\post-conditions.
- If you wish to test a particular method rather than all the methods in a
  file, you can specify such a method by using the `/testTargetMethod` command line
  argument and providing the fully qualified method name.
- If you are using `/testTargetMethod` and would like to inline methods that are
  called from the method of interest, you can do so by setting
  `/testInlineDepth` to something larger than zero (zero is the default). The
  `/verifyAllModules` argument might also be relevant if the methods to be
  inlined are defined in included files.
- To deal with loops, you should use `/loopUnroll` and also `/testSeqLengthLimit`.
  The latter argument adds an axiom that limits the length of any sequence to
  be no greater than some specified value. This restriction can be used to
  ensure that the number of loop unrolls is sufficient with respect to the
  length of any input sequence but it can also cause the program to miss
  certain corner cases.

## How to Run Tests?

To run the tests, you would first need to compile the code to some other
language. Once this is done, the main difficulty is to mock the arguments
that the test methods take. The following code (to be inserted into the class
with the tests) should do the job in Java:

```java
public static void main(String[] args) throws Exception {
  for (Method method: CLASS_WITH_TESTS.class.getDeclaredMethods()) {
    if (!method.getName().startsWith("test"))
      continue;
    Object result = method.invoke(null, mockParameters(method));
    String resultString = result == null ? "null" : result.toString();
    System.out.println(method.getName() + " " + resultString);
  }
}


public static Object[] mockParameters(Method method) {
    Object[] parameters = null;;
    try {
        Class<?>[] types = method.getParameterTypes();
        parameters = new Object[types.length];
        for (int i = 0; i < types.length; i++)
            parameters[i] = types[i].getConstructor().newInstance();
    } catch (Exception e) {
        e.printStackTrace();
    }
    return parameters;
}
```

## Example

Below is a simple example of what test generation will do to a file called `Char.dfy` with the following code:
```
module Char {
  method compareToB(c: char) returns (i: int) {
    if (c == 'B') {
        return 0;
    } else if (c > 'B') {
        return 1;
    } else {
        return -1;
    }
  }
}
```
Running test generation like this:

```dafny /definiteAssignment:3 /testMode:Block Char.dfy ```

Will give the following list of tests (tabulation added manually):
```
include "Char.dfy"
module CharUnitTests {
  import Char
  method test0() returns (r0:int)  {
    r0 := Char.compareToB('!');
  }
  method test1() returns (r0:int)  {
    r0 := Char.compareToB(']');
  }
  method test2() returns (r0:int)  {
    r0 := Char.compareToB('B');
  }
}
```

Compiling this to Java and, after inserting the code shown
[above](#how-to-run-tests), compiling and running the resulting Java code
yields the following output:

```
test2 0
test1 1
test0 -1
```