// RUN: %resolve --rprint:%t.rprint "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Type =
  | SelfOwned
  | U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128
  | TIdentifier(name: string)
  | TMemberSelect(base: Type, name: string)
  | TypeApp(baseName: Type, arguments: seq<Type>)
  | Borrowed(underlying: Type)
  | BorrowedMut(underlying: Type)
  | ImplType(underlying: Type)
  | DynType(underlying: Type)
  | TupleType(arguments: seq<Type>)
  | FnType(arguments: seq<Type>, returnType: Type)
  | IntersectionType(left: Type, right: Type)

datatype DeclareType = MUT | CONST

datatype Expr =
    RawExpr(content: string)
  | Identifier(name: string) // Can be empty for global in MemberSelect
  //| Match(matchee: Expr, cases: seq<MatchCase>)
  | StmtExpr(stmt: Expr, rhs: Expr)
  | Block(underlying: Expr)
  //| StructBuild(name: string, assignments: seq<AssignIdentifier>)
  | Tuple(arguments: seq<Expr>)
  | UnaryOp(op1: string, underlying: Expr, format: UnaryOpFormat)
  | BinaryOp(op2: string, left: Expr, right: Expr, format2: BinaryOpFormat)
  | LiteralInt(value: string)
  | LiteralString(value: string, binary: bool)
  | ConversionNum(tpe: Type, underlying: Expr)
  | DeclareVar(declareType: DeclareType, name: string, optType: Option<Type>, optRhs: Option<Expr>)
  | AssignVar(name: string, rhs: Expr)
  | Call(obj: Expr, typeParameters: seq<Type>, arguments: seq<Expr>)
  | Select(obj: Expr, name: string)
  | MemberSelect(obj: Expr, name: string)
{
    function Optimize(): Expr
    {
      match this {
        case UnaryOp("&", Call(Select(underlying, "clone"), typeArgs, args), format) =>
          if typeArgs == [] && args == [] then
            UnaryOp("&", underlying, format)
          else
            this

        case UnaryOp("!", BinaryOp("==", left, right, format),
          CombineFormat()) =>
          BinaryOp("!=", left, right, BinaryOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, NoFormat()),
          CombineFormat()) =>
          BinaryOp(">=", left, right, BinaryOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, ReverseFormat()),
          CombineFormat()) =>
          BinaryOp("<=", right, left, BinaryOpFormat.NoFormat())

        case ConversionNum(tpe, expr) =>
          if || tpe.U8? || tpe.U16? || tpe.U32? || tpe.U64? || tpe.U128?
             || tpe.I8? || tpe.I16? || tpe.I32? || tpe.I64? || tpe.I128? then
            match expr {
              case Call(MemberSelect(
                MemberSelect(MemberSelect(
                Identifier(""), "dafny_runtime"), "DafnyInt"), "from"), tpe, args) =>
                if |tpe| == 0 && |args| == 1 then
                  match args[0] {
                    case LiteralInt(number) => LiteralInt("/*optimized*/"+number)
                    case LiteralString(number, _) => LiteralInt("/*optimized*/"+number)
                    case _ => this
                  }
                else this
              case _ => this
            }
          else
            this
        case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(AssignVar(name2, rhs), last)) =>
          if name == name2 then
            var rewriting := StmtExpr(DeclareVar(mod, name, Some(tpe), Some(rhs)), last);
            rewriting
          else
            this
        case _ => this
      }
    }
}

datatype UnaryOpFormat =
  | NoFormat
  | CombineFormat
datatype BinaryOpFormat =
  | NoFormat
  | ImpliesFormat
  | EquivalenceFormat
  | ReverseFormat

datatype Option<+T> = None | Some(value: T) {
  
  function UnwrapOr(default: T): T {
    match this
    case Some(v) => v
    case None() => default
  }

  predicate IsFailure() {
    None?
  }

  function PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }

  function Extract(): T
    requires Some?
  {
    value
  }
}