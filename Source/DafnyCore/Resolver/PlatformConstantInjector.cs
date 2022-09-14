using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class PlatformConstantInjector : IRewriter {

  public PlatformConstantInjector(ErrorReporter reporter) : base(reporter) {
  }

  /// <summary>
  /// TODO
  /// </summary>
  internal override void PreResolve(ModuleDefinition m) {
    foreach(var d in m.TopLevelDecls) {
      if (d is TopLevelDeclWithMembers decl && decl.Name == "Dafny") {
        foreach(var member in decl.Members) {
          if (member is ConstantField cf && member.Name == "SIZE_T_LIMIT") {
            
            
          }
        }
      }
    }
  }

  private class ConstantInjectingCloner : Cloner {
    public virtual Field CloneField(Field f) {
      Contract.Requires(f != null);
      if (f is ConstantField c && c.Name == "SIZE_T_LIMIT") {
        var sizeNativeTypeName = DafnyOptions.O.Compiler.SizeNativeType;
        var sizeNativeType = Resolver.NativeTypes.First(nt => nt.Name == sizeNativeTypeName);
        var rhs = new LiteralExpr(c.tok, sizeNativeType.UpperBound);
        return new ConstantField(Tok(c.tok), c.Name, rhs, c.HasStaticKeyword, c.IsGhost, CloneType(c.Type), CloneAttributes(c.Attributes));
      }
      
      return base.CloneField(f);
    }
  }
}