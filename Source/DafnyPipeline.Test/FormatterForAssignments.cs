using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForAssignments")]
public class FormatterForAssignments : FormatterBaseTest {
  [Fact]
  public void FormatterWorksForAssignments() {
    FormatterWorksFor(@"method test() {
  var
    x
    :=
    1;
  var y := 3;
  x := 2;
  x :=
    3;
  x := 4
    ;
  x
    := 4;
  x
    :=
    4;
  x, y :=
    2, 3;
}");
  }
  [Fact]
  public void FormatterWorksForVarAssignments() {
    FormatterWorksFor(@"
method Test() {
  var y,
      z
    := x,
       1;
  var
    x
    ,
    y
    :=
    2
    ,
    3
    ;
  var x :=
    2;
  var
    x :=
    2;
  var z
    , 
      w
    :=
    4
    ,
    5
    ;
  var b
    , c
    := d
     , e;
  var y
    , z :=
    x
    , 1;
  var
    y,
    z
    :=
    x
    ,1;
  var w :|
    true;
}
");
  }

  [Fact]
  public void FormatterWorksForObjectCreation() {
    FormatterWorksFor(@"
method Test() {
  g := new ClassName.ConstructorName(
    argument1b,
    argument2b,
    argument3b
  );
  var g := new ClassName.ConstructorName(
    argument1,
    argument2,
    argument3
  );
  g :=
    Datatype.ConstructorName(
      argumentd2,
      argumente2,
      argumentf2
    );
  var g := Datatype.ConstructorName(
    argumenta,
    argumentb,
    argumentc
  );
  :- Module.Need(
    arg1,
    arg2
  );
  var g, h := Datatype.ConstructorName1(
      argumentaz
    ),
    Datatype.ConstructorName2(
      argumentaw
    )
    ;
  g, h := Datatype.ConstructorName1(
      argumentbz
    ),
    Datatype.ConstructorName2(
      argumentbw
    )
    ;
  var g :=
    Datatype.ConstructorName(
      argumentd,
      argumente,
      argumentf
    );
  g := Datatype.ConstructorName(
    argumenta2,
    argumentb2,
    argumentc2
  );
  var h :=
    new ClassName.ConstructorName2(
      argument4,
      argument5,
      argument6
    );
  h :=
    new ClassName.ConstructorName2(
      argument4b,
      argument5b,
      argument6b
    );
}
", reduceBlockiness: true);
  }
  [Fact]
  public void FormatterWorksForObjectCreationBlockly() {
    FormatterWorksFor(@"
method Test() {
  :- Module.Need(
       arg3,
       arg4
     );
  var g := new ClassName.ConstructorName(
             argument1,
             argument2,
             argument3
           );
  var g := Datatype.ConstructorName(
             argumenta,
             argumentb,
             argumentc
           );

  var g :=
    Datatype.ConstructorName(
      argumentd,
      argumente,
      argumentf
    );
  var h :=
    new ClassName.ConstructorName2(
      argument4,
      argument5,
      argument6
    );
}
", reduceBlockiness: false);
  }

  public FormatterForAssignments([NotNull] ITestOutputHelper output) : base(output)
  {
  }
}
