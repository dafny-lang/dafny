using System.Threading.Tasks;
using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForTopLevelDeclarations")]
public class FormatterForAtAttributes : FormatterBaseTest {
  [Fact]
  public async Task FormatterWorksForMemberDeclAtAttributes() {
    await FormatterWorksFor(@"
module Enclosing {
  @ResourceLimit(""1500e3"")
  @IsolateAssertions
  lemma ReplaceDotsInvertible(i: string)

  @IsolateAssertions
  @Compile(true)
  type X = Int

  @IsolateAssertions
  @Compile(true)
  type Xsub = x: Int | x != 0

  @IsolateAssertions
  @Compile(true)
  type AbstractType

  @IsolateAssertions
  @Compile(true)
  datatype Y = YCons()

  @IsolateAssertions
  @Compile(true)
  codatatype Y = YCons()

  @Compile(false)
  @Compile(true)
  module SubModule {
  }

  @Compile(false)
  @Compile(true)
  const Two := 2

  class Test {
    @ResourceLimit(""2500e3"")
    @IsolateAssertions
    lemma ReplaceDotsInvertible(i: string)

    @ResourceLimit(""3500e3"")
    @IsolateAssertions
    function OtherFunction(i: string): string

    @ResourceLimit(""4500e3"")
    @IsolateAssertions
    static
    lemma ReplaceDotsInvertible(i: string)

    @Compile(false)
    @Compile(true)
    const Two := 2
  }
}
", null, true);
  }

  public FormatterForAtAttributes([NotNull] ITestOutputHelper output) : base(output) {
  }
}
