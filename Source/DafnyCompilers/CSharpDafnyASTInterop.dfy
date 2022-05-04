include "CSharpDafnyASTModel.dfy"

module {:extern "CSharpDafnyASTInterop"} CSharpDafnyASTInterop {
  import CSharpDafnyASTModel

  class {:extern} TypeUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} NormalizeExpand(ty: CSharpDafnyASTModel.Type)
      : CSharpDafnyASTModel.Type
  }
}
