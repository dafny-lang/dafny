﻿using System.Threading.Tasks;
using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForApplySuffixRelated")]
public class FormatterForApplySuffixRelated : FormatterBaseTest {
  [Fact]
  public async Task FormatterWorksForArguments() {
    await FormatterWorksFor(@"
method Test()
{
  me(func(arg(5,
              6
             ,7
          )
     )
  );

  me(func(arg(3,
              4)));

  me(func(arg(
            8, 9)));

  me(func(
       arg(
         10, 11)));

  me(
    func(
      arg(
        12, 13)),
    func2());
  me
  (func
   (arg
    (1
    ,2)),
   func2());
}
");
  }

  public FormatterForApplySuffixRelated([NotNull] ITestOutputHelper output) : base(output) {
  }
}
