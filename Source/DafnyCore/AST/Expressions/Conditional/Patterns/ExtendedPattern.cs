#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/*
ExtendedPattern is either:
1 - A LitPattern of a LiteralExpr, representing a constant pattern
2 - An IdPattern of a string and a list of ExtendedPattern, representing either
    a bound variable or a constructor applied to n arguments or a symbolic constant
*/
public abstract class ExtendedPattern : NodeWithOrigin {
  public bool IsGhost;

  [SyntaxConstructor]
  public ExtendedPattern(IOrigin origin, bool isGhost = false) : base(origin) {
    IsGhost = isGhost;
  }

  public IEnumerable<Node> DescendantsAndSelf =>
    new[] { this }.Concat(Children.OfType<ExtendedPattern>().SelectMany(c => c.DescendantsAndSelf));

  public virtual IEnumerable<Expression> SubExpressions {
    get {
      yield break;
    }
  }

  public abstract void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext,
    Type sourceType, bool isGhost, bool inStatementContext,
    bool inPattern, bool inDisjunctivePattern);

  /*
  *  Ensures that all ExtendedPattern held in NestedMatchCase are linear
  *  Uses provided type to determine if IdPatterns are datatypes (of the provided type) or variables
  *  pat could be
  *  0 - A DisjunctivePattern
  *  1 - An IdPattern (without argument) at base type
  *  2 - A LitPattern at base type
  *  3* - An IdPattern at tuple type representing a tuple
  *  3 - An IdPattern at datatype type representing a constructor of type
  *  4 - An IdPattern at datatype type with no arguments representing a bound variable
  */
  public void CheckLinearExtendedPattern(Type? type, ResolutionContext resolutionContext, ModuleResolver resolver) {
    if (type == null) {
      return;
    }

    if (this is DisjunctivePattern dp) {
      foreach (var alt in dp.Alternatives) {
        // Pushing a scope silences the “duplicate parameter” error in
        // `CheckLinearVarPattern`.  This is acceptable because disjunctive
        // patterns are not allowed to bind variables (the corresponding
        // error is raised in `RemoveDisjunctivePatterns`).
        resolver.scope.PushMarker();
        alt.CheckLinearExtendedPattern(type, resolutionContext, resolver);
        resolver.scope.PopMarker();
      }
    } else if (!type.IsDatatype) { // Neither tuple nor datatype
      if (this is IdPattern idPattern) {
        if (idPattern.Arguments != null) {
          // pat is a tuple or constructor
          if (idPattern.Id.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
            resolver.reporter.Error(MessageSource.Resolver, this.Origin, $"tuple type does not match type {type.ToString()}");
          } else {
            resolver.reporter.Error(MessageSource.Resolver, this.Origin, $"member {idPattern.Id} does not exist in type {type.ToString()}");
          }
        } else { // pat is a simple variable or a constant
          /* =[1]= */
          idPattern.CheckLinearVarPattern(type, resolutionContext, resolver);
        }
        return;
      } else if (this is LitPattern) { // pat is a literal
        /* =[2]= */
        return;
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();
      }
    } else if (type.AsDatatype is TupleTypeDecl tupleTypeDecl) {
      if (!(this is IdPattern)) {
        resolver.reporter.Error(MessageSource.Resolver, this.Origin, "pattern doesn't correspond to a tuple");
        return;
      }

      var udt = (UserDefinedType)type.NormalizeExpand();
      IdPattern idpat = (IdPattern)this;
      if (idpat.Arguments == null) {
        // simple variable
        idpat.CheckLinearVarPattern(udt, resolutionContext, resolver);
        return;
      }

      Contract.Assert(tupleTypeDecl.Ctors.Count == 1);
      Contract.Assert(tupleTypeDecl.Ctors[0] == tupleTypeDecl.GroundingCtor);
      idpat.Ctor = tupleTypeDecl.GroundingCtor;

      if (idpat.Id != tupleTypeDecl.GroundingCtor.Name) {
        if (idpat.Id.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
          resolver.reporter.Error(MessageSource.Resolver, this.Origin,
            $"the case pattern is a {idpat.Arguments.Count}-element tuple, while the match expression is a {udt.TypeArgs.Count}-element tuple");
        } else {
          resolver.Reporter.Error(MessageSource.Resolver, idpat.Origin,
            $"found constructor {idpat.Id} but expected a {tupleTypeDecl.Dims}-tuple");
        }
      }

      var pairTP = udt.TypeArgs.Zip(idpat.Arguments, (x, y) => new Tuple<Type, ExtendedPattern>(x, y));

      foreach (var tp in pairTP) {
        var t = resolver.PartiallyResolveTypeForMemberSelection(this.Origin, tp.Item1).NormalizeExpand();
        tp.Item2.CheckLinearExtendedPattern(t, resolutionContext, resolver);
      }
      return;
    } else { // matching a datatype value
      if (!(this is IdPattern)) {
        Contract.Assert(this is LitPattern);
        resolver.reporter.Error(MessageSource.Resolver, this.Origin, "Constant pattern used in place of datatype");
        return;
      }
      IdPattern idpat = (IdPattern)this;

      var dtd = type.AsDatatype;
      Dictionary<string, DatatypeCtor> ctors = dtd.ConstructorsByName;
      if (ctors == null) {
        Contract.Assert(false); throw new Cce.UnreachableException();  // Datatype not found
      }
      // Check if the head of the pattern is a constructor or a variable
      if (ctors.TryGetValue(idpat.Id, out var ctor)) {
        Contract.Assert(ctor != null);
        /* =[3]= */
        idpat.Ctor = ctor;
        if (idpat.Arguments == null && ctor.Formals.Count == 0) {
          // nullary constructor without () -- so convert it to a constructor
          idpat.MakeAConstructor();
        }
        if (idpat.Arguments == null) {
          // pat is a variable
          return;
        } else if (ctor.Formals.Count == idpat.Arguments.Count) {
          if (ctor.Formals.Count == 0) {
            // if nullary constructor
            return;
          } else {
            // if non-nullary constructor
            var subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, type.NormalizeExpand().TypeArgs);
            var argTypes = ctor.Formals.ConvertAll<Type>(x => x.Type.Subst(subst));
            var pairFA = argTypes.Zip(idpat.Arguments, (x, y) => new Tuple<Type, ExtendedPattern>(x, y));
            foreach (var fa in pairFA) {
              // get DatatypeDecl of Formal, recursive call on argument
              fa.Item2.CheckLinearExtendedPattern(fa.Item1, resolutionContext, resolver);
            }
          }
        } else {
          // else applied to the wrong number of arguments
          resolver.reporter.Error(MessageSource.Resolver, "ConstructorWrongArity", idpat.Origin,
            "constructor {0} of arity {2} is applied to {1} argument(s)",
            idpat.Id, (idpat.Arguments?.Count ?? 0).ToString(), ctor.Formals.Count.ToString());
        }
      } else {
        /* =[4]= */
        // pattern is a variable OR error (handled in CheckLinearVarPattern)
        idpat.CheckLinearVarPattern(type, resolutionContext, resolver);
      }
    }
  }
}