// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using DafnyTestGeneration.Inlining;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test; 

public class Inlining : Setup {

  private readonly TextWriter output;

  public Inlining(ITestOutputHelper output) {
    this.output = new WriterFromOutputHelper(output);
  }

  private static string RemoveSpaces(string input) {
    return Regex.Replace(input, "[ \t\n]", "");
  }

  private void ShortCircuitRemovalTest(string source, string expectedResult, bool isByMethod = true) {
    var options = GetDafnyOptions(new List<Action<DafnyOptions>>(), output);
    var program = Utils.Parse(options, source, false);
    var boogieProgram = InliningTranslator.TranslateAndInline(program, options);
    var method = program.DefaultModuleDef.Children
      .OfType<TopLevelDeclWithMembers>().First(classDef => classDef.Children.Count() != 0)?
      .Children.OfType<Method>().First();
    Assert.NotNull(method);
    Assert.Equal(isByMethod, method.IsByMethod);
    var writer = new StringWriter();
    new Printer(writer, options).PrintStatement(method.Body, 0);
    var result = RemoveSpaces(writer.ToString());
    Assert.Equal(RemoveSpaces(expectedResult), result);
    Assert.False(program.Reporter.HasErrors);
    boogieProgram.Resolve(options);
  }

  [Fact]
  public void FunctionToFunctionByMethod() {
    var source = @"
function {:testEntry} Identity(i:int):int {
  i
}
".TrimStart();
    var expectedResult = "{ return i; }";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveShortCircuitingAnd() {
    var source = @"
predicate {:testEntry} And(a:bool, b:bool) {
  a && b
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var expectedResult = $"{{ var {tmpVar} : bool; {tmpVar} := a; if {tmpVar} {{ {tmpVar} := b; }} else {tmpVar} := {tmpVar}; return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveShortCircuitingOr() {
    var source = @"
predicate {:testEntry} And(a:bool, b:bool) {
  a || b
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var expectedResult = $"{{ var {tmpVar} : bool; {tmpVar} := a; if !{tmpVar} {{ {tmpVar} := b; }} else {tmpVar} := {tmpVar}; return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveShortCircuitingImp() {
    var source = @"
predicate {:testEntry} And(a:bool, b:bool) {
  a ==> b
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var expectedResult =
      $"{{ var {tmpVar} : bool; {tmpVar} := a; if {tmpVar} {{ {tmpVar} := b; }} else {tmpVar} := true; return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveShortCircuitingExp() {
    var source = @"
predicate {:testEntry} And(a:bool, b:bool) {
  a <== b
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var expectedResult = $"{{ var {tmpVar} : bool; {tmpVar} := a; if {tmpVar} {{ {tmpVar} := b; }} else {tmpVar} := true; return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveShortCircuitingIfThenElse() {
    var source = @"
function {:testEntry} And(a:bool):int {
  if a then 1 else 2
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var expectedResult = $"{{ var {tmpVar}; if a {{ {tmpVar} := 1; }} else {tmpVar} := 2; return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveLet() {
    var source = @"
function {:testEntry} And(a:bool):int {
  var a:int := 7; a
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var expectedResult = $"{{ var {tmpVar}; {{ var a := 7; {tmpVar} := a; }} return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveNestedLet() {
    var source = @"
function {:testEntry} And(a:bool):int {
  var a:real := 7.5; var a:int := 4; a
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    var expectedResult = $"{{ var {tmpVar}; {{ var a := 7.5; var {tmpVar2}; {{ var a := 4; {tmpVar2} := a; }} {tmpVar} := {tmpVar2}; }} return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveIfInsideLet() {
    var source = @"
function {:testEntry} And(a:bool):int {
  var a := false; if a then 5 else 7
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    var expectedResult = $"{{ var {tmpVar}; {{ var a := false; var {tmpVar2}; if a {{ {tmpVar2} := 5; }} else {tmpVar2} := 7; {tmpVar} := {tmpVar2}; }} return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveShortCircuitInElseBranch() {
    var source = @"
function {:testEntry} And(a:bool, b:bool):int {
  if a then 5 else if b then 3 else 1
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    var expectedResult = $"{{ var {tmpVar}; if a {{ {tmpVar} := 5; }} else {{ var {tmpVar2}; if b {{ {tmpVar2} := 3; }} else {tmpVar2} := 1; {tmpVar} := {tmpVar2}; }} return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveStmtExpression() {
    var source = @"
function {:testEntry} And(a:int):int {
  if (var a := true; a) then 5 else 3
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    var expectedResult = $"{{ var {tmpVar}; var {tmpVar2}; {{ var a := true; {tmpVar2} := a; }} if {tmpVar2} {{ {tmpVar} := 5; }} else {tmpVar} := 3; return {tmpVar}; }}";
    ShortCircuitRemovalTest(source, expectedResult);
  }

  [Fact]
  public void RemoveSimpleMatch() {
    var source = @"
datatype Option = None | Some
function {:testEntry} IsNone(o: Option): bool {
  match o
    case None => true
    case Some => false
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    ShortCircuitRemovalTest(source, $"{{ var {tmpVar}; match o case {{:split false}} None() => {tmpVar} := true; case {{:split false}} Some() =>  {tmpVar} := false; return {tmpVar}; }}");
  }

  [Fact]
  public void RemoveMatchWithDestructors() {
    var source = @"
datatype Option = None | Some(val:int)
function {:testEntry} UnBoxOrZero(o: Option): int {
  match o
    case None => 0
    case Some(r) => r
}
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    ShortCircuitRemovalTest(source, $"{{ var {tmpVar}; match o case {{:split false}} None() => {tmpVar} := 0; case {{:split false}} Some(r) =>  {tmpVar} := r; return {tmpVar}; }}");
  }

  [Fact]
  public void LiftFunctionCall() {
    var source = @"
function {:testEntry} Max(a:int, b:int):int {
  -Min(-a, -b)
}
function Min(a:int, b:int):int { if a < b then a else b }
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    ShortCircuitRemovalTest(source, $"{{ var {tmpVar}; {tmpVar} := Min(-a, -b); return -{tmpVar}; }}");
  }

  [Fact]
  public void LiftNestedFunctionCall() {
    var source = @"
function {:testEntry} Max(a:int, b:int):int {
  Negate(Min(Negate(a), Negate(b)))
}
function Negate(a:int):int   { -a }
function Min(a:int, b:int):int { if a < b then a else b }
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    var tmpVar3 = RemoveShortCircuitingCloner.TmpVarPrefix + 2;
    var tmpVar4 = RemoveShortCircuitingCloner.TmpVarPrefix + 3;
    ShortCircuitRemovalTest(source, $"{{ var {tmpVar}; var {tmpVar2}; var {tmpVar3}; {tmpVar3} := Negate(a); var {tmpVar4}; {tmpVar4} := Negate(b); {tmpVar2} := Min({tmpVar3}, {tmpVar4}); {tmpVar} := Negate({tmpVar2}); return {tmpVar}; }}");
  }

  [Fact]
  public void LiftFunctionCallWithShortCircuitingArgs() {
    var source = @"
function {:testEntry} Max(a:bool, b:bool):bool {
  IsTrue(a || b)
}
function IsTrue(a:bool):bool { a }
".TrimStart();
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    ShortCircuitRemovalTest(source, $"{{ var {tmpVar}; var {tmpVar2}:bool; {tmpVar2} := a; if !{tmpVar2} {{ {tmpVar2} := b; }} else {tmpVar2} := {tmpVar2}; {tmpVar} := IsTrue({tmpVar2}); return {tmpVar}; }}");
  }
  
  [Fact]
  public void ProcessConstructor() {
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
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    var tmpVar2 = RemoveShortCircuitingCloner.TmpVarPrefix + 1;
    ShortCircuitRemovalTest(source, $"{{ var {tmpVar}; if true then {{ {tmpVar} := 0; }} else {tmpVar} := 1; i := {tmpVar}; var {tmpVar2}; if true then {{ {tmpVar2} := 0; }} else {tmpVar2} := 1; i := {tmpVar2};}}", isByMethod:false);
  }

  [Fact]
  public void ProcessWhileStmt() {
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
    var tmpVar = RemoveShortCircuitingCloner.TmpVarPrefix + 0;
    ShortCircuitRemovalTest(source, $"{{ var i := 0; s := 0; var {tmpVar}; {{var n:= n; {tmpVar} := i <= n;}} while {tmpVar} decreases n-i {{s := s+i; i:= i+1; {{var n:= n; {tmpVar} := i <= n;}}}} return s;}}", false);
  }

}
