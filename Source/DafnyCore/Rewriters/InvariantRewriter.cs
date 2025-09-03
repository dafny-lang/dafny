namespace Microsoft.Dafny;

public class InvariantRewriter(ErrorReporter reporter) : IRewriter(reporter) {
  internal override void PostResolve(ModuleDefinition moduleDefinition) {
    foreach (var decl in moduleDefinition.TopLevelDecls) {
      // If a class has an invariant, then it needs at least one constructor (in whose body the invariant will be asserted)
      // In order for the invariant to be inductive over the transition system of the program
      // Otherwise, a false invariant will lead to an inconsistency
      if (decl is ClassDecl { HasConstructor: false } cd and TopLevelDeclWithMembers { Invariant: not null }) {
        reporter.Error(MessageSource.Resolver, cd, "a class with an invariant must have at least one user-defined constructor");
      }
    }
  }
}