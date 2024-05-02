using System;

namespace Microsoft.Dafny.Compilers {

  class BuilderSyntaxTree<T> : ConcreteSyntaxTree {
    public readonly T Builder;
    public readonly DafnyCodeGenerator Compiler;

    public BuilderSyntaxTree(T builder, DafnyCodeGenerator compiler) {
      if (builder == null) {
        throw new ArgumentNullException(nameof(builder));
      }

      Builder = builder;
      Compiler = compiler;
    }

    public override ConcreteSyntaxTree Fork(int relativeIndent = 0) {
      if (Builder is StatementContainer statementContainer) {
        return new BuilderSyntaxTree<StatementContainer>(statementContainer.Fork(), Compiler);
      } else {
        // Warning: this is an invalid operation: cannot fork builder of type Builder.GetType()
        throw new InvalidOperationException("<i>Builder not StatementContainer</i> but " + Builder.GetType().ToString());
      }
    }

    public override ConcreteSyntaxTree ForkInParens() {
      // TODO(shadaj): perhaps should check if we are an expr container
      return new BuilderSyntaxTree<T>(Builder, Compiler);
    }

    public override ConcreteSyntaxTree NewBlock(string header = "", string footer = "",
      BlockStyle open = BlockStyle.SpaceBrace,
      BlockStyle close = BlockStyle.NewlineBrace) {
      return Fork();
    }
  }
}
