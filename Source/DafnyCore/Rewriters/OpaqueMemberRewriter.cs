using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// For any function foo() with the :opaque attribute,
/// hide the body, so that it can only be seen within its
/// recursive clique (if any), or if the programmer
/// specifically asks to see it via the reveal_foo() lemma
/// </summary>
public class OpaqueMemberRewriter : IRewriter {
  protected Dictionary<Method, Function> revealOriginal; // Map reveal_* lemmas (or two-state lemmas) back to their original functions

  public OpaqueMemberRewriter(ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);

    revealOriginal = new Dictionary<Method, Function>();
  }

  internal override void PreResolve(ModuleDefinition m) {
    foreach (var d in m.TopLevelDecls) {
      if (d is TopLevelDeclWithMembers) {
        ProcessOpaqueClassMembers((TopLevelDeclWithMembers)d);
      }
    }
  }

  internal override void PostResolveIntermediate(ModuleDefinition m) {
    foreach (var decl in ModuleDefinition.AllCallables(m.TopLevelDecls)) {
      if (decl is Lemma or TwoStateLemma) {
        var lem = (Method)decl;
        if (revealOriginal.ContainsKey(lem)) {
          var fn = revealOriginal[lem];
          AnnotateRevealFunction(lem, fn);
        }
      }
    }
  }

  protected void AnnotateRevealFunction(Method lemma, Function f) {
    Contract.Requires(lemma is Lemma || lemma is TwoStateLemma);
    Expression receiver;
    if (f.IsStatic) {
      receiver = new StaticReceiverExpr(f.tok, (TopLevelDeclWithMembers)f.EnclosingClass, true);
    } else {
      receiver = new ImplicitThisExpr(f.tok);
      //receiver.Type = GetThisType(expr.tok, (TopLevelDeclWithMembers)member.EnclosingClass);  // resolve here
    }
    var typeApplication = new List<Type>();
    var typeApplication_JustForMember = new List<Type>();
    for (int i = 0; i < f.TypeArgs.Count; i++) {
      // doesn't matter what type, just so we have it to make the resolver happy when resolving function member of
      // the fuel attribute. This might not be needed after fixing codeplex issue #172.
      typeApplication.Add(new IntType());
      typeApplication_JustForMember.Add(new IntType());
    }
    var nameSegment = new NameSegment(f.tok, f.Name, f.TypeArgs.Count == 0 ? null : typeApplication);
    var rr = new MemberSelectExpr(f.tok, receiver, f.Name);
    rr.Member = f;
    rr.TypeApplication_AtEnclosingClass = typeApplication;
    rr.TypeApplication_JustMember = typeApplication_JustForMember;
    List<Type> args = new List<Type>();
    for (int i = 0; i < f.Formals.Count; i++) {
      args.Add(new IntType());
    }
    rr.Type = new ArrowType(f.tok, args, new IntType());
    nameSegment.ResolvedExpression = rr;
    nameSegment.Type = rr.Type;
    LiteralExpr low = new LiteralExpr(f.tok, 1);
    LiteralExpr hi = new LiteralExpr(f.tok, 2);
    lemma.Attributes = new Attributes("fuel", new List<Expression>() { nameSegment, low, hi }, lemma.Attributes);
  }


  // Tells the function to use 0 fuel by default
  protected void ProcessOpaqueClassMembers(TopLevelDeclWithMembers c) {
    Contract.Requires(c != null);
    var newDecls = new List<MemberDecl>();
    foreach (var member in c.Members.Where(member => member is Function or ConstantField)) {
      if (!Attributes.Contains(member.Attributes, "opaque") && !member.IsOpaque) {
        // Nothing to do
      } else if (!RefinementToken.IsInherited(member.tok, c.EnclosingModuleDefinition)) {
        GenerateRevealLemma(member, newDecls);
      }
    }
    c.Members.AddRange(newDecls);
  }

  private void GenerateRevealLemma(MemberDecl m, List<MemberDecl> newDecls) {
    if (m is Function f) {
      // mark the opaque function with {:fuel 0, 0}
      var amount = new LiteralExpr(m.tok, 0);
      m.Attributes = new Attributes("fuel", new List<Expression>() { amount, amount }, m.Attributes);

      // That is, given:
      //   function {:opaque} foo(x:int, y:int) : int
      //     requires 0 <= x < 5;
      //     requires 0 <= y < 5;
      //     ensures foo(x, y) < 10;
      //   { x + y }
      // We produce:
      //   lemma {:axiom} {:auto_generated} {:fuel foo, 1, 2 } reveal_foo()
      //
      // If "foo" is a two-state function, then "reveal_foo" will be declared as a two-state lemma.
      //
      // The translator, in AddMethod, then adds ensures clauses to bump up the fuel parameters appropriately

      var cloner = new Cloner();

      List<TypeParameter> typeVars = new List<TypeParameter>();
      List<Type> optTypeArgs = new List<Type>();
      foreach (var tp in f.TypeArgs) {
        typeVars.Add(cloner.CloneTypeParam(tp));
        // doesn't matter what type, just so we have it to make the resolver happy when resolving function member of
        // the fuel attribute. This might not be needed after fixing codeplex issue #172.
        optTypeArgs.Add(new IntType());
      }
    }

    // Given:
    //   const {:opaque} foo := x
    // We produce:
    //   lemma {:auto_generated} {:opaque_reveal} {:verify false} reveal_foo()
    //     ensures foo == x

    // Add an axiom attribute so that the compiler won't complain about the lemma's lack of a body
    Attributes lemma_attrs = null;
    if (m is Function) {
      lemma_attrs = new Attributes("axiom", new List<Expression>(), lemma_attrs);
    }
    lemma_attrs = new Attributes("auto_generated", new List<Expression>(), lemma_attrs);
    lemma_attrs = new Attributes("opaque_reveal", new List<Expression>(), lemma_attrs);
    lemma_attrs = new Attributes("verify", new List<Expression>() { new LiteralExpr(m.tok, false) }, lemma_attrs);
    var ens = new List<AttributedExpression>();
    if (m is ConstantField c && c.Rhs != null) {
      ens.Add(new AttributedExpression(new BinaryExpr(c.tok, BinaryExpr.Opcode.Eq, new NameSegment(c.Tok, c.Name, null), c.Rhs)));
    }
    Method reveal;
    if (m is TwoStateFunction) {
      reveal = new TwoStateLemma(m.RangeToken, m.NameNode.Prepend("reveal_"), m.HasStaticKeyword, new List<TypeParameter>(), new List<Formal>(), new List<Formal>(), new List<AttributedExpression>(),
        new Specification<FrameExpression>(new List<FrameExpression>(), null), ens,
        new Specification<Expression>(new List<Expression>(), null), null, lemma_attrs, null);
    } else {
      reveal = new Lemma(m.RangeToken, m.NameNode.Prepend("reveal_"), m.HasStaticKeyword, new List<TypeParameter>(), new List<Formal>(), new List<Formal>(), new List<AttributedExpression>(),
        new Specification<FrameExpression>(new List<FrameExpression>(), null), ens,
        new Specification<Expression>(new List<Expression>(), null), null, lemma_attrs, null);
    }
    newDecls.Add(reveal);
    reveal.InheritVisibility(m, true);
    if (m is Function fn) {
      revealOriginal[reveal] = fn;
    }
  }
}
