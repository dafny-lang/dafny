# Test Generation for Dafny

[**Purpose**](#purpose) <br>
[**General Approach**](#general-approach) <br>
[**Implementation**](#implementation) <br>
[**How to Generate Tests?**](#how-to-generate-tests) <br>
[**How to Run Tests?**](#how-to-run-tests) <br>
[**Dead Code Identification Example**](#dead-code-identification-example)

## Purpose

Block- and path-coverage tests of Dafny code can be used to:
- Identify dead code (see [example](#dead-code-identification-example)).
- Test the implementation of unverified external methods by increasing one's assurance that compiled tests produce no errors when run.
- Increase assurance that Dafny and Java (C#, Rust, etc.) implementations of some functionality are equivalent by generating tests in Dafny and comparing the results of running these tests on compiled Dafny and original Java (C#, Rust, etc.).

## General Approach

To generate a test that covers a particular basic block or path, we add an assertion to the target method that is violated in the event that a particular block is visited or a particular path is taken. We then use the counterexample model provided by the prover to extract the inputs to the target method that cause the assertion violation, which gives us the desired test case.

While these manipulations could be done with the Dafny source directly, we instead modify the Boogie translation, since it is much easier to work with basic blocks and paths on this lower level.

We currently provide no oracle against which to compare the result. In the future, it may be possible to generate an oracle directly from the prover model provided that there is no non-determinism in the tested code.


## Implementation

- [Main.cs](Main.cs) - contains the two methods that should be used to query Dafny to generate tests.
- [Utils.cs](Utils.cs) - a small collection of utility methods used elsewhere in the project.
- [TestMethod.cs](TestMethod.cs) - generates a test that calls the target method with arguments triggering an assertion violation described by Z3's counterexample model. This is where all the interaction with DafnyServer's counterexample extraction code takes place.
- [ProgramModification.cs](ProgramModification.cs) - represents a modification of the original Boogie program (which is in turn generated in `Main.cs` by translating Dafny input to Boogie). Can be verified and, if verification fails, one can pass the counterexample log as constructor argument to `TestMethod`.
- [ProgramModifier.cs](ProgramModifier.cs) - an abstract class that contains utilities for annotating Boogie Programs, inlining Dafny methods after they are translated to Boogie, etc. This is all necessary for generating instances of `ProgramModification`
- [BlockBasedModifier.cs](BlockBasedModifier.cs) and [PathBasedModifier.cs](PathBasedModifier.cs) - subclasses of `ProgramModifier` that generate instances of `ProgramModification` by inserting assertions that fail when a particular block is visited or a particular path is taken, respectively.
- [DafnyInfo.cs](DafnyInfo.cs) - takes a Dafny Program and extracts certain information about it that is then used in `TestMethod.cs` and `Main.cs`

## How to Generate Tests?

- Test generation currently works with all basic types, user-defined classes, sequences, sets, and maps. Not counting several edge cases, it also works with datatypes. It does not currently work on arrays or multisets. It is also not possible to generate tests for constructors. Please avoid top-level methods and wrap them inside classes or modules.
- To generate block- or path-coverage tests use the `/generateTestMode:Block` or `/generateTestMode:Path` arguments respectively. Test generation relies on Dafny to generate Boogie implementations and Dafny does not generate a Boogie implementation when there are no proof obligations, so no tests will be generated in the latter scenario (so you might want to use /definiteAssignment:3).
- If you wish to test a particular method rather than all the methods in a file, you can specify such a method with the `/generateTestTargetMethod` command line argument and providing the fully qualified method name.
- If you are using `/generateTestTargetMethod` and would like to inline methods that are called from the method of interest, you can do so by setting `/generateTestInlineDepth` to something larger than zero (zero is the default). The `/verifyAllModules` argument might also be relevant if the methods to be inlined are defined in included files.
- To deal with loops, you should use `/loopUnroll` and also `/generateTestSeqLengthLimit`. The latter argument adds an axiom that limits the length of any sequence to be no greater than some specified value. This restriction can be used to ensure that the number of loop unrolls is sufficient with respect to the length of any input sequence but it can also cause the program to miss certain corner cases.
- The`/warnDeadCode` argument will make Dafny identify potential dead code in the specified file. Note that false negatives are possible if `/loopUnroll` is not used. False positives are also possible for a variety of reasons, such as `/loopUnroll` being assigned not high enough value.
- You can use `/generateTestVerbose` and `/generateTestPrintBpl:FILENAME.bpl` for debugging purposes.

## How to Run Tests?

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
The tests can be generated like this:

```dafny /definiteAssignment:3 /generateTestMode:Block object.dfy ```

Dafny will give the following list of tests as output (tabulation added manually):
```dafny
include "object.dfy"
module objectUnitTests {
  import M
  method {:test} test0() {
    var v0 := getFreshMValue();
    v0.v := -39;
    var r0 := M.compareToZero(v0);
  }
  method {:test} test1() {
    var v0 := getFreshMValue();
    v0.v := 39;
    var r0 := M.compareToZero(v0);
  }
  method {:test} test2() {
    var v0 := getFreshMValue();
    v0.v := 0;
    var r0 := M.compareToZero(v0);
  }
  method {:synthesize} getFreshMValue() 
    returns (o:M.Value) 
    ensures fresh(o)
}
```

Saving these tests in a file `test.dfy` and compiling the code to C# using `dafny /compileVerbose:1 /compile:0 /spillTargetCode:3 /noVerify test.dfy` produces a file `test.cs`. 

You can then run `dotnet test YourCSProjectFile.csproj` to execute the tests.

Note that your `.csproj` file must include `xunit` and `Moq` libraries. You can use this template:

```
<Project Sdk="Microsoft.NET.Sdk">

  <PropertyGroup>
    <TargetFramework>net6.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
    <IsPackable>false</IsPackable>
  </PropertyGroup>

  <ItemGroup>
    <PackageReference Include="Microsoft.NET.Test.Sdk" Version="16.11.0" />
    <PackageReference Include="xunit" Version="2.4.1" />
    <PackageReference Include="xunit.runner.visualstudio" Version="2.4.3">
      <IncludeAssets>runtime; build; native; contentfiles; analyzers; buildtransitive</IncludeAssets>
      <PrivateAssets>all</PrivateAssets>
    </PackageReference>
    <PackageReference Include="Moq" Version="4.16.1" />	   
  </ItemGroup>		  
</Project>

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
