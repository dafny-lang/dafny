using System;

namespace Microsoft.Dafny.Compilers {

  class BuilderSyntaxTree<T> : ConcreteSyntaxTree {
    public readonly T Builder;

    public BuilderSyntaxTree(T builder) {
      if (builder == null) {
        throw new ArgumentNullException(nameof(builder));
      }

      Builder = builder;
    }

    public override ConcreteSyntaxTree Fork(int relativeIndent = 0) {
      if (Builder is StatementContainer statementContainer) {
        return new BuilderSyntaxTree<StatementContainer>(statementContainer.Fork());
      } else {
        DafnyCodeGenerator.ThrowGeneralUnsupported(); // Warning: this is an invalid operation: cannot fork builder of type Builder.GetType()
        throw new InvalidOperationException();
      }
    }

    public override ConcreteSyntaxTree ForkInParens() {
      // TODO(shadaj): perhaps should check if we are an expr container
      return new BuilderSyntaxTree<T>(Builder);
    }
  }
}
