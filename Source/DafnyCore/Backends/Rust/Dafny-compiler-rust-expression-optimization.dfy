// Tests in Dafny-compiler-rust-coverage
module ExpressionOptimization {
  import Std
  import opened RAST
  import opened DAST.Format
  import opened Std.Wrappers

  function apply(mod: Mod): Mod {
    ExprSimplifier().ReplaceMod(mod, crate.MSel(mod.name))
  }

  function ExprSimplifier(): RASTBottomUpReplacer
  {
    RASTBottomUpReplacer(
      ReplaceModSingle :=
        (m: Mod, SelfPath: Path) => m,
      ReplaceTypeSingle := (t: Type) => t,
      ReplaceExprSingle :=
        (e: Expr) =>
          match e {
            case UnaryOp("!", BinaryOp(op, left, right, format),
              CombineFormat()) =>
              match op {
                case "==" => BinaryOp("!=", left, right, BinaryOpFormat.NoFormat())
                case "<" =>
                  if format.NoFormat? then
                    BinaryOp(">=", left, right, BinaryOpFormat.NoFormat())
                  else if format.ReverseFormat? then
                    BinaryOp("<=", right, left, BinaryOpFormat.NoFormat())
                  else
                    e
                case _ => e
              }
            case Call(ExprFromPath(PMemberSelect(r, "truncate!")), args) =>
              if (r != dafny_runtime && r != global) || |args| != 2  then
                e
              else
                var expr := args[0];
                var tpeExpr := args[1];
                if !tpeExpr.ExprFromType? then e else
                var tpe := tpeExpr.tpe;
                if || tpe.U8? || tpe.U16? || tpe.U32? || tpe.U64? || tpe.U128?
                  || tpe.I8? || tpe.I16? || tpe.I32? || tpe.I64? || tpe.I128? || tpe.USIZE? then
                  match expr {
                    case Call(ExprFromPath(PMemberSelect(base, "int!")), args) =>
                      if |args| == 1 && (base == dafny_runtime || base == global) then
                        match args[0] {
                          case LiteralInt(number) => LiteralInt(number)
                          case LiteralString(number, _, _) => LiteralInt(number)
                          case _ => e
                        }
                      else e
                    case _ => e
                  }
                else
                  e
            case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(Assign(name2, rhs), last)) =>
              if name2 == Some(LocalVar(name)) then
                StmtExpr(DeclareVar(mod, name, Some(tpe), Some(rhs)), last)
              else
                e
            case StmtExpr(IfExpr(UnaryOp("!", BinaryOp("==", a, b, f), uf), maybePanic, RawExpr("")), last) =>
              if EndsWithPanic(maybePanic) then
                StmtExpr(Identifier("assert_eq!").Apply([a, b]), last)
              else
                e
            case _ => e
          }
          
    )
  }

  predicate EndsWithPanic(maybePanic: Expr) {
    match maybePanic {
      case StmtExpr(stmt, rhs) => EndsWithPanic(rhs)
      case Call(Identifier("panic!"), args) => 
        if |args| == 1 then
          match args[0] {
            case LiteralString("Halt", _, _) => true
            case _ => false
          }
        else
          false
      case _ => false
    }
  }
}
