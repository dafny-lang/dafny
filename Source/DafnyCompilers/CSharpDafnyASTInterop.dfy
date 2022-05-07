include "CSharpDafnyASTModel.dfy"

module {:extern "CSharpDafnyASTInterop"} CSharpDafnyASTInterop {
  import CSharpDafnyASTModel

  function {:axiom} TypeHeight(t: CSharpDafnyASTModel.Type) : nat

  function {:axiom} ASTHeight(c: object) : nat
    requires || c is CSharpDafnyASTModel.Expression
             || c is CSharpDafnyASTModel.Statement

  class {:extern} TypeUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} NormalizeExpand(ty: CSharpDafnyASTModel.Type)
      : (ty': CSharpDafnyASTModel.Type)
      ensures TypeHeight(ty') <= TypeHeight(ty)
  }
}
