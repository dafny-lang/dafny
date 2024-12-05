// Tests
module {:extern "DefsCoverage"} DafnyToRustCompilerDefinitionsCoverage {
  import opened DafnyToRustCompilerDefinitions
  import opened DAST
  import Strings = Std.Strings
  import Std
  import opened Std.Wrappers
  import R = RAST
  import opened DafnyCompilerRustUtils

  const IND := R.IND
  type Type = DAST.Type
  type Formal = DAST.Formal

  method Expect(x: bool)
  {
    expect x; // Avoids having too little coverage
  }

  method Tests() {
    Expect(SurelyAssigned.Join(SurelyAssigned) == SurelyAssigned);
    Expect(NotAssigned.Join(NotAssigned) == NotAssigned);
    Expect(NotAssigned.Join(SurelyAssigned) == Unknown);
    Expect(SurelyAssigned.Join(NotAssigned) == Unknown);
    Expect(Unknown.Join(NotAssigned) == NotAssigned.Join(Unknown) == Unknown);
    Expect(Unknown.Join(SurelyAssigned) == SurelyAssigned.Join(Unknown) == Unknown);
    Expect(Unknown.Join(Unknown) == Unknown);

    Expect(SurelyAssigned.Then(Unknown)
        == SurelyAssigned.Then(NotAssigned)
        == SurelyAssigned.Then(SurelyAssigned)
        == NotAssigned.Then(SurelyAssigned)
        == SurelyAssigned);
    Expect(Unknown.Then(NotAssigned)
        == Unknown.Then(SurelyAssigned)
        == Unknown.Then(Unknown)
        == NotAssigned.Then(Unknown)
        == Unknown);
    Expect(NotAssigned.Then(NotAssigned)
           == NotAssigned);

    var x := VarName("x");
    var y := VarName("y");
    var z := Expression.Ident(VarName("z"));
    var assigns_x := [Assign(AssignLhs.Ident(x), Expression.Ident(y))];
    var assigns_y := [Assign(AssignLhs.Ident(y), Expression.Ident(x))];
    var cond := Expression.Ident(VarName("cond"));
    var unknown_x := [If(cond, assigns_x, assigns_y)];
    var surely_double_x := [If(cond, assigns_x, assigns_x)];
    var call_to_x := [Statement.Call(z, SetBuilderAdd, [], [], Some([x]))];
    var declare_x_again := [DeclareVar(x, Type.Tuple([]), None)];
    Expect(DetectAssignmentStatus(assigns_y, x) == NotAssigned);
    Expect(DetectAssignmentStatus(assigns_x, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus(assigns_x, y) == NotAssigned);
    Expect(DetectAssignmentStatus(assigns_x + assigns_y, y) == SurelyAssigned);
    Expect(DetectAssignmentStatus(unknown_x, x) == Unknown);
    Expect(DetectAssignmentStatus(surely_double_x, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus(surely_double_x, y) == NotAssigned);
    Expect(DetectAssignmentStatus(call_to_x, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus(call_to_x, y) == NotAssigned);
    Expect(DetectAssignmentStatus(call_to_x + assigns_y, y) == SurelyAssigned);
    Expect(DetectAssignmentStatus([Labeled("l", assigns_y)] + assigns_x, y) == SurelyAssigned);
    Expect(DetectAssignmentStatus([Labeled("l", assigns_x)] + assigns_y, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus([Labeled("l", assigns_x)] + assigns_y, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus(declare_x_again + assigns_x, x) == NotAssigned);
    Expect(DetectAssignmentStatus(declare_x_again + assigns_y, y) == SurelyAssigned);
    Expect(DetectAssignmentStatus([Return(z)] + assigns_x, x) == NotAssigned);
    Expect(DetectAssignmentStatus([EarlyReturn()] + assigns_x, x) == NotAssigned);
    Expect(DetectAssignmentStatus([JumpTailCallStart()] + assigns_x, x) == NotAssigned);
    Expect(DetectAssignmentStatus([Print(z)] + assigns_x, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus([Print(z)] + assigns_x, x) == SurelyAssigned);
    Expect(DetectAssignmentStatus([While(z, [])] + assigns_x, x) == Unknown);
    Expect(DetectAssignmentStatus([If(cond, assigns_x, [If(cond, assigns_x, assigns_y)])], x) == Unknown);
    Expect(
      DetectAssignmentStatus(
        [ If(cond,
             [If(cond, [Return(z)], [])] +
             assigns_x,
             [If(cond,
                 [If(cond, [Return(z)], [])] +
                 assigns_x,
                 assigns_y)])], x) == Unknown);
  }
}