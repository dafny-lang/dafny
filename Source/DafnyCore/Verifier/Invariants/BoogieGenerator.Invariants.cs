namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private void AddInvariantsWellformednessCheck(ClassLikeDecl c) {
    // It would be nice if we could just emit a dummy predicate, reading this,
    // containing the invariants as a conjunction
    // But that would result in poor error messages
    new ClassLikeDeclWellformednessChecker(this, c).Check();
  }
}