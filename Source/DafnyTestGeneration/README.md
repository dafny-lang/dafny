# Test Generation for Dafny

[**Purpose**](#purpose) <br>
[**General Approach**](#general-approach) <br>
[**Implementation**](#implementation) <br>
[**How to Generate and Run Tests?**](#how-to-generate-and-run-tests) <br>
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

## How to Generate and Run Tests?

Run `dafny generate-tests` to get the list of all supported options.

To consider a simple example, suppose you have a file called `object.dfy` with the following code:
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

```dafny generate-tests Block object.dfy```

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
module M {
  method m(a:int) returns (b:int)
    requires a > 0
  {
    if (a == 0) {
      return 0;
    }
    return 1;
  }
}
```

Running dead code identification like this:

`dafny find-dead-code Sample.dfy`

Will give the following information:

```
Code at Sample.dfy(6,14) is potentially unreachable.
Out of 3 basic blocks (3 capturedStates), 2 (2) are reachable.
There might be false negatives if you are not unrolling loops.
False positives are always possible.
```
