// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration.Inlining;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test;

public class ShortCircuitRemoval : Setup {

  private readonly TextWriter output;

  public ShortCircuitRemoval(ITestOutputHelper output) {
    this.output = new WriterFromOutputHelper(output);
  }

  private static string RemoveSpaces(string input) {
    return Regex.Replace(input, "[ \t\n\r]", "");
  }

  /// <summary>
  /// Perform shared checks and return the target method for further testing on a case by case basis
  /// </summary>
  private async Task<MethodOrConstructor> ShortCircuitRemovalTest(string source, string expected, bool isByMethod = true) {
    // If the following assertion fails, rename the corresponding variables in expected output of each test
    Assert.Equal(RemoveShortCircuitingRewriter.TmpVarPrefix, "#tmp");
    var options = GetDafnyOptions([], output);
    var program = await Parse(new BatchErrorReporter(options), source, false);
    var success = InliningTranslator.TranslateForFutureInlining(program, options, out var boogieProgram);
    Assert.True(success);
    var method = program.DefaultModuleDef.Children
      .OfType<TopLevelDeclWithMembers>()
      .Select(classDef => classDef.Members.Where(member => member is MethodOrConstructor &&
        member.HasUserAttribute(TestGenerationOptions.TestEntryAttribute, out var _)))?
      .Where(members => members.Count() != 0).FirstOrDefault()?.First() as MethodOrConstructor;
    Assert.NotNull(method);
    Assert.Equal(isByMethod, (method is Method { IsByMethod: true }));
    var writer = new StringWriter();
    new Printer(writer, options).PrintStatement(method.Body, 0);
    var result = RemoveSpaces(writer.ToString());
    Assert.Equal(RemoveSpaces(expected), result);
    Assert.False(program.Reporter.HasErrors);
    boogieProgram.Resolve(options);
    return method;
  }

  [Fact]
  public async Task FunctionToFunctionByMethod() {
    var source = @"
function {:testEntry} Identity(i:int):int {
  i
}
".TrimStart();
    var expected = "{ return i; }";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task And() {
    var source = @"
predicate {:testEntry} And(a:bool, b:bool) {
  a && b
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0 : bool; 
  #tmp0 := a; 
  if #tmp0 { 
    #tmp0 := b; 
  } else 
    #tmp0 := #tmp0; 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task Or() {
    var source = @"
predicate {:testEntry} Or(a:bool, b:bool) {
  a || b
}
".TrimStart();
    var expected = @"
{
  var #tmp0 : bool;
  #tmp0 := a;
  if !#tmp0 { 
    #tmp0 := b; 
  } else 
    #tmp0 := #tmp0; 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task Imp() {
    var source = @"
predicate {:testEntry} Imp(a:bool, b:bool) {
  a ==> b
}
".TrimStart();
    var expected =
      @"
{ 
  var #tmp0 : bool; 
  #tmp0 := a; 
  if #tmp0 { 
    #tmp0 := b; 
  } else 
    #tmp0 := true; 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task Exp() {
    var source = @"
predicate {:testEntry} Exp(a:bool, b:bool) {
  a <== b
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0 : bool; 
  #tmp0 := a; 
  if #tmp0 { 
    #tmp0 := b; 
  } else 
    #tmp0 := true; 
  return #tmp0;
 }";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task IfThenElse() {
    var source = @"
function {:testEntry} IfThenElse(a:bool):int {
  if a then 1 else 2
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  if a { 
    #tmp0 := 1; 
  } else 
    #tmp0 := 2; 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task Let() {
    var source = @"
function {:testEntry} Let(a:bool):int {
  var a:int := 7; a
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  { 
    var a := 7;
    #tmp0 := a;
  }
  return #tmp0;
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task NestedLet() {
    var source = @"
function {:testEntry} NestedLet(a:bool):int {
  var a:real := 7.5; var a:int := 4; a
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  { 
    var a := 7.5;
    var #tmp1; 
    { 
      var a := 4; 
      #tmp1 := a; 
    } 
    #tmp0 := #tmp1; 
  } 
return #tmp0; }";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task IfInsideLet() {
    var source = @"
function {:testEntry} Let(a:bool):int {
  var a := false; if a then 5 else 7
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  { 
    var a := false; 
    var #tmp1; 
    if a { 
      #tmp1 := 5; 
    } else
      #tmp1 := 7;
    #tmp0 := #tmp1; 
  } 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task InElseBranch() {
    var source = @"
function {:testEntry} NestedIfTheElse(a:bool, b:bool):int {
  if a then 5 else if b then 3 else 1
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  if a { 
    #tmp0 := 5; 
  } else { 
    var #tmp1; 
    if b { 
      #tmp1 := 3; 
    } else 
      #tmp1 := 1; 
    #tmp0 := #tmp1; 
  } 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task StmtExpression() {
    var source = @"
function {:testEntry} StmtExpression(a:int):int {
  if (var a := true; a) then 5 else 3
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  var #tmp1; 
  { var a := true; #tmp1 := a; } 
  if #tmp1 { 
    #tmp0 := 5; 
  } else 
    #tmp0 := 3; 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task Match() {
    var source = @"
datatype Option = None | Some
function {:testEntry} IsNone(o: Option): bool {
  match o
    case None => true
    case Some => false
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  match o 
    case {:split false} None() =>  #tmp0 := true; 
    case {:split false} Some() =>  #tmp0 := false; 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task MatchWithDestructors() {
    var source = @"
datatype Option = None | Some(val:int)
function {:testEntry} UnBoxOrZero(o: Option): int {
  match o
    case None => 0
    case Some(r) => r
}
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  match o 
    case {:split false} None() =>   #tmp0 := 0; 
    case {:split false} Some(r) =>  #tmp0 := r; 
  return #tmp0;
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task FunctionCall() {
    var source = @"
function {:testEntry} Max(a:int, b:int):int {
  -Min(-a, -b)
}
function Min(a:int, b:int):int { if a < b then a else b }
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  #tmp0 := Min(-a, -b); 
  return -#tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task NestedFunctionCall() {
    var source = @"
function {:testEntry} Max(a:int, b:int):int {
  Negate(Min(Negate(a), Negate(b)))
}
function Negate(a:int):int   { -a }
function Min(a:int, b:int):int { if a < b then a else b }
".TrimStart();
    var expected = @"
{ 
  var #tmp0; 
  var #tmp1; 
  var #tmp2; 
  #tmp2 := Negate(a); 
  var #tmp3; 
  #tmp3 := Negate(b); 
  #tmp1 := Min(#tmp2, #tmp3); 
  #tmp0 := Negate(#tmp1); 
  return #tmp0; 
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task FunctionCallWithShortCircuitingArgs() {
    var source = @"
function {:testEntry} Arguments(a:bool, b:bool):bool {
  IsTrue(a || b)
}
function IsTrue(a:bool):bool { a }
".TrimStart();
    var expected = @"
{
  var #tmp0;
  var #tmp1:bool;
  #tmp1 := a;
  if !#tmp1 {
    #tmp1 := b;
  } else 
    #tmp1 := #tmp1;
  #tmp0 := IsTrue(#tmp1);
  return #tmp0;
}";
    await ShortCircuitRemovalTest(source, expected);
  }

  [Fact]
  public async Task Constructor() {
    var source = @"
class C {
  var i:int
  constructor {:testEntry} C() { 
    i := if true then 0 else 1;
    new;
    i := if true then 0 else 1;
  }
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  if true {
    #tmp0 := 0;
  } else
    #tmp0 := 1;
  i := #tmp0;
  new;
  var #tmp1;
  if true {
    #tmp1 := 0;
  } else
    #tmp1 := 1;
  i := #tmp1;
}";
    await ShortCircuitRemovalTest(source, expected, isByMethod: false);
  }

  [Fact]
  public async Task While() {
    var source = @"
method {:testEntry} Sum(n:int) returns (s:int)
  requires n >= 0
{
  var i := 0;
  s := 0;
  while (var n := n; i <= n)
    decreases n-i;
  {
    s := s + i;
    i := i + 1;
  }
  return s;
}
".TrimStart();
    var expected = @"
{
  var i := 0;
  s := 0;
  var #tmp0; 
  { var n:= n; #tmp0 := i <= n; } 
  while #tmp0 
    decreases n-i 
  {
    s := s+i;
    i:= i+1; 
    { var n:= n; #tmp0 := i <= n;}
  } 
  return s;
}";
    await ShortCircuitRemovalTest(source, expected, false);
  }

  [Fact]
  public async Task LetOrFail() {
    var source = @"
datatype Result<T> = Success(value:T) | Failure {
  predicate IsFailure() {true}
  function PropagateFailure():Result<T> {this}
}
function {:testInline 1} Fail():Result<bool> {Failure}
function {:testEntry} EntryLetOrFail():Result<bool> {
  :- Fail(); Success(true)
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  { 
    :- Fail();
    #tmp0 := Success(true);
  }
  return #tmp0;
}";
    var resultingMethod = await ShortCircuitRemovalTest(source, expected);
    Assert.True(resultingMethod.Body.Body[1] is BlockStmt);
    var blockStmt = resultingMethod.Body.Body[1] as BlockStmt;
    Assert.True(blockStmt.Body[0] is AssignOrReturnStmt);
    var assignOrReturn = blockStmt.Body[0] as AssignOrReturnStmt; // :- Fail() prior to desugaring
    Assert.True(assignOrReturn.Children.ToList()[1] is AssignStatement);
    var updateStmt = assignOrReturn.Children.ToList()[1] as AssignStatement; // := Fail(), which is part of desugaring
    Assert.Contains(updateStmt.ResolvedStatements, statement => statement is CallStmt); // Fail() is a method call
  }

  [Fact]
  public async Task LetOrFailWithAssignment() {
    var source = @"
datatype Result<T> = Success(value:T) | Failure {
  predicate IsFailure() {true}
  function PropagateFailure():Result<T> {this}
  function Extract():T requires !IsFailure() {value}
}
function {:testInline 1} Fail():Result<bool> {Failure}
function {:testEntry} EntryLetOrFail():Result<bool> {
  var x :- Fail(); Success(x)
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  { 
    var x :- Fail();
    #tmp0 := Success(x);
  }
  return #tmp0;
}";
    var resultingMethod = await ShortCircuitRemovalTest(source, expected);
    Assert.True(resultingMethod.Body.Body[1] is BlockStmt);
    var blockStmt = resultingMethod.Body.Body[1] as BlockStmt;
    Assert.True(blockStmt.Body[0] is VarDeclStmt);
    var varDeclStmt = blockStmt.Body[0] as VarDeclStmt; // x :- Fail() prior to desugaring
    Assert.True(varDeclStmt.Assign.Children.ToList()[1] is AssignStatement);
    var updateStmt = varDeclStmt.Assign.Children.ToList()[1] as AssignStatement; // x := Fail(), which is part of desugaring
    Assert.Contains(updateStmt.ResolvedStatements, statement => statement is CallStmt); // Fail() is a method call
  }

  [Fact]
  public async Task TypeRhs() {
    var source = @"
class A { 
  constructor () {}
}
method {:testEntry} allocateA() {
  var a := new A();
}
".TrimStart();
    var expected = @"
{
  var a := new A();
}";
    await ShortCircuitRemovalTest(source, expected, false);
  }

  [Fact]
  public async Task Print() {
    var source = @"
method {:testEntry} Print(b:bool) {
  print if b then ['a', 'b', 'c'] else [];
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  if b {
    #tmp0 := ['a', 'b', 'c'];
  } else
    #tmp0 := [];
  print #tmp0;
}";
    await ShortCircuitRemovalTest(source, expected, false);
  }

  [Fact]
  public async Task ForLoop() {
    var source = @"
method {:testEntry} Sum(n:int) returns (s:int)
  requires n >= 0
{
  s := 0;
  for i := 0 to (var n:=n-1; n+1) {
    s := s + i;
  }
  return s;
}
".TrimStart();
    var expected = @"
{
  s := 0;
  var #tmp0; 
  { var n := n - 1; #tmp0 := n + 1; }
  for i:int := 0 to #tmp0 {
    s := s + i;
  }
  return s;
}";
    await ShortCircuitRemovalTest(source, expected, false);
  }

  [Fact]
  public async Task CallStmt() {
    var source = @"
method callee(a:int) {}
method {:testEntry} caller() {
  callee(if false then 0 else 1);
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  if false { 
    #tmp0 := 0;
  } else
    #tmp0 := 1;
  callee(#tmp0);
}";
    await ShortCircuitRemovalTest(source, expected, false);
  }

  [Fact]
  public async Task CallStmtWithUpdate() {
    var source = @"
method callee(a:int) returns (i:int) { return a; }
method {:testEntry} caller() {
  var x := callee(if false then 0 else 1);
}
".TrimStart();
    var expected = @"
{
  var #tmp0;
  if false { 
    #tmp0 := 0;
  } else
    #tmp0 := 1;
  var x := callee(#tmp0);
}";
    await ShortCircuitRemovalTest(source, expected, false);
  }

}
