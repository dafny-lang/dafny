# Test Generation for Dafny

[**Purpose**](#purpose) <br>
[**General Approach**](#general-approach) <br>
[**Implementation**](#implementation) <br>
[**How to Generate Tests?**](#how-to-generate-tests) <br>
[**How to Run Tests?**](#how-to-run-tests) <br>
[**Example**](#example) <br>
[**Dead Code Identification Example**](#dead-code-identification-example)

## Purpose

Block- and path-coverage tests of Dafny code can be used to:
- Identify dead code (see [example](#dead-code-identification-example)).
- Test the implementation of unverified external methods by increasing one's assurance that compiled tests produce no errors when run.
- Increase assurance that Dafny and Java (C#, Rust, etc.) implementations of some functionality are equivalent by generating tests in Dafny and comparing the results of running these tests on compiled Dafny and original Java (C#, Rust, etc.).

## General Approach

To generate a test that covers a particular basic block or path, we add an assertion to the target method that is violated in the event that a particular block is visited or a particular path is taken. We then use the counterexample model provided by the prover to extract the inputs to the target method that cause the assertion violation, which gives us the desired test case.

While these manipulations could be done with the Dafny source directly, we instead modify the Boogie translation, since it is much easier to work with basic blocks and paths on this lower level.

Objects present an obstacle for test generation since it is not possible to mock objects in Dafny and the prover model does not specify how an object was allocated\constructed. Currently, we require that a test method take any object it needs as an argument. This allows us to compile the test methods to Java or another language where object mocking is possible (see [How to Run Tests?](#how-to-run-tests)).

Even though it is possible to run the tests in this way, we currently provide no oracle against which to compare the result. In the future, it may be possible to generate an oracle directly from the prover model provided that there is no non-determinism in the tested code.


## Implementation

- [Main.cs](Main.cs) - contains the two methods that should be used to query Dafny to generate tests.
- [Utils.cs](Utils.cs) - a small collection of utility methods used elsewhere in the project.
- [TestMethod.cs](TestMethod.cs) - generates a test that calls the target method with arguments triggering an assertion violation described by Z3's counterexample model. This is where all the interaction with DafnyServer's counterexample extraction code takes place.
- [ProgramModification.cs](ProgramModification.cs) - represents a modification of the original Boogie program (which is in turn generated in `Main.cs` by translating Dafny input to Boogie). Can be verified and, if verification fails, one can pass the counterexample log as constructor argument to `TestMethod`.
- [ProgramModifier.cs](ProgramModifier.cs) - an abstract class that contains utilities for annotating Boogie Programs, inlining Dafny methods after they are translated to Boogie, etc. This is all necessary for generating instances of `ProgramModification`
- [BlockBasedModifier.cs](BlockBasedModifier.cs) and [PathBasedModifier.cs](PathBasedModifier.cs) - subclasses of `ProgramModifier` that generate instances of `ProgramModification` by inserting assertions that fail when a particular block is visited or a particular path is taken, respectively.
- [DafnyInfo.cs](DafnyInfo.cs) - takes a Dafny Program and extracts certain information about it that is then used in `TestMethod.cs` and `Main.cs`

## How to Generate Tests?

- Test generation currently works with all basic types, user-defined classes, sequences, sets, and maps. It does not work with datatypes, arrays, and multisets. It is also not possible to generate tests for constructors. Please avoid top-level methods and wrap them inside classes or modules.
- To generate block- or path-coverage tests use the `/generateTestMode:Block` or `/generateTestMode:Path` arguments respectively. Test generation relies on Dafny to generate Boogie implementations and Dafny does not generate a Boogie implementation when there are no proof obligations, so no tests will be generated in the latter scenario.
- If you wish to test a particular method rather than all the methods in a file, you can specify such a method with the `/generateTestTargetMethod` command line argument and providing the fully qualified method name.
- If you are using `/generateTestTargetMethod` and would like to inline methods that are called from the method of interest, you can do so by setting `/generateTestInlineDepth` to something larger than zero (zero is the default). The `/verifyAllModules` argument might also be relevant if the methods to be inlined are defined in included files.
- To deal with loops, you should use `/loopUnroll` and also `/generateTestSeqLengthLimit`. The latter argument adds an axiom that limits the length of any sequence to be no greater than some specified value. This restriction can be used to ensure that the number of loop unrolls is sufficient with respect to the length of any input sequence but it can also cause the program to miss certain corner cases.
- The`/warnDeadCode` argument will make Dafny identify potential dead code in the specified file. Note that false negatives are possible if `/loopUnroll` is not used. False positives are also possible for a variety of reasons, such as `/loopUnroll` being assigned not high enough value.

## How to Run Tests?

To run the tests, you would first need to compile the code to some other language. Once this is done, the main difficulty is to mock the arguments that the test methods take. The following code (to be inserted into the class with the tests) should do the job in Java (you would also need to add `import java.lang.reflect.*;` at the top of the file):

```java
public static void main(String[] args) throws Exception {
  for (Method method: __default.class.getDeclaredMethods()) {
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

Suppose you have a file called `object.dfy` with the following code:
```dafny
module M {
  class Value {
    var v:int;
  }
  method compareToZero(v:Value) returns (i:int) {
    if (v.v == 0) {
      return 0;
    } else if (v.v > 0) {
      return 1;
    }
    return -1;
  }
}
```
The tests can be run like this (in this particular case, `/definiteAssignment:3` adds proof obligations that cause the Dafny to Boogie translator to emit an implementation for the target method):

```dafny /definiteAssignment:3 /generateTestMode:Block object.dfy ```

Dafny will give the following list of tests as output (tabulation added manually):
```dafny
include "object.dfy"
module objectUnitTests {
  import M
  method test0(v0:M.Value) returns (r0:int)  modifies v0 {
    v0.v := -39;
    r0 := M.compareToZero(v0);
  }
  method test1(v0:M.Value) returns (r0:int)  modifies v0 {
    v0.v := 39;
    r0 := M.compareToZero(v0);
  }
  method test2(v0:M.Value) returns (r0:int)  modifies v0 {
    v0.v := 0;
    r0 := M.compareToZero(v0);
  }
}
```

Saving these tests in a file `test.dfy` and compiling the code to Java using `dafny /compileTarget:java test.dfy` produces directory `test-java`. The tests are located in `test-java/objectUnitTests_Compile/__default.java`. To run the tests, it is first necessary to add the code shown [above](#how-to-run-tests) to the file with the tests. The code can then be compiled to bytecode using:

```
javac -cp PATH_TO_DafnyRuntime.jar:test-java test-java/objectUnitTests_Compile/__default.java
```

Finally, running the code with `java -cp PATH_TO_DafnyRuntime.jar:test-java objectUnitTests_Compile/__default` yields:

```
test1 1
test0 -1
test2 0
```

## Dead Code Identification Example

Suppose you have a file called "Sample.dfy" with the following code:

```dafny
method m(a:int) returns (b:int)
  requires a > 0
{
  if (a == 0) {
    return 0;
  }
  return 1;
}
```

Running dead code identification like this:

`dafny /warnDeadCode /definiteAssignment:3 ../examples/Sample.dfy`

Will give the following information:

```
Code at ../examples/Sample.dfy(5,12) is potentially unreachable.
Out of 5 basic blocks (3 capturedStates), 4 (2) are reachable.
There might be false negatives if you are not unrolling loops.
False positives are always possible.
```