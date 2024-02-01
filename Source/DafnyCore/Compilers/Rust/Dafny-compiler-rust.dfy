include "../Dafny/AST.dfy"
// Dafny to Rust compilation tenets:
// - The Compiled Dafny AST should be minimal
// - The generated code should look idiomatic and close to the original Dafny file if possible

// Rust AST
module RAST {
  import opened Std.Wrappers
  import opened Std.Strings
  import opened DAST.Format

  const IND := "  "
  // Indentation level
  /* trait ModDecl {} */

  datatype Mod /*extends ModDecl*/ =
      // Rust modules
    | Mod(name: string, body: seq<ModDecl>)
    | ExternMod(name: string)
  {
    function ToString(ind: string): string
      decreases this
    {
      match this {
        case ExternMod(name) =>
          "mod " + name + ";"
        case Mod(name, body) =>
          "mod " + name + " {" + "\n" + ind + IND +
          SeqToString(
            body,
            (modDecl: ModDecl) requires modDecl < this =>
              modDecl.ToString(ind + IND), "\n" + ind + IND)
          + "\n" + ind + "}"
      }
    }
  }
  function SeqToString<T>(s: seq<T>, f: T --> string, separator: string := ""): string
    requires forall t <- s :: f.requires(t)
  {
    if |s| == 0 then "" else
    f(s[0]) + (if |s| > 1 then separator + SeqToString(s[1..], f, separator) else "")
  }
  function SeqToHeight<T>(s: seq<T>, f: T --> nat): (r: nat)
    requires forall t <- s :: f.requires(t)
    ensures forall t <- s :: f(t) <= r
  {
    if |s| == 0 then 0 else
    var i := f(s[0]);
    var j := SeqToHeight(s[1..], f);
    if i < j then j else i
  }
  datatype ModDecl =
    | RawDecl(body: string)
    | ModDecl(mod: Mod)
    | StructDecl(struct: Struct)
    | EnumDecl(enum: Enum)
    | ImplDecl(impl: Impl)
    | TraitDecl(tr: Trait)
  {
    function ToString(ind: string): string
      decreases this
    {
      if ModDecl? then mod.ToString(ind)
      else if StructDecl? then struct.ToString(ind)
      else if ImplDecl? then impl.ToString(ind)
      else if EnumDecl? then enum.ToString(ind)
      else if TraitDecl? then tr.ToString(ind)
      else assert RawDecl?; body
    }
  }
  datatype Attribute = RawAttribute(content: string) {
    static function ToStringMultiple(attributes: seq<Attribute>, ind: string): string {
      SeqToString(
        attributes,
        (attribute: Attribute) => attribute.content + "\n" + ind)
    }
  }

  datatype Struct =
    Struct(attributes: seq<Attribute>,
           name: string, typeParams: seq<TypeParam>, fields: Formals)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub struct " + name +
      TypeParam.ToStringMultiple(typeParams, ind) +
      fields.ToString(ind + IND, fields.NamedFormals?) +
      (if fields.NamelessFormals? then ";" else "")
    }
  }

  datatype NamelessFormal =
    NamelessFormal(visibility: VISIBILITY, tpe: Type)
  {
    function ToString(ind: string): string {
      (if visibility == PUB then "pub " else "") + tpe.ToString(ind)
    }
  }

  datatype Formals =
    | NamedFormals(fields: seq<Formal>)
    | NamelessFormals(types: seq<NamelessFormal>)
  {
    function ToString(ind: string, newLine: bool): string {
      if NamedFormals? then
        var separator := if newLine then ",\n" + ind + IND else ", ";
        var (beginSpace, endSpace) :=
          if newLine && |fields| > 0 then
            ("\n" + ind + IND, "\n" + ind)
          else if |fields| > 0 then
            (" ", " ")
          else
            ("", "");
        " {" + beginSpace +
        SeqToString(fields, (field: Formal) => field.ToString(ind + IND), separator)
        + endSpace + "}"
      else
        assert NamelessFormals?;
        var separator := if newLine then ",\n" + ind + IND else ", ";
        "("+
        SeqToString(types, (t: NamelessFormal) => t.ToString(ind + IND), separator)
        +")"
    }
  }

  datatype EnumCase =
    | EnumCase(name: string, fields: Formals)
  {
    function ToString(ind: string, newLine: bool): string {
      name + fields.ToString(ind, newLine)
    }
  }

  datatype Enum =
    Enum(attributes: seq<Attribute>,
         name: string, typeParams: seq<TypeParam>,
         variants: seq<EnumCase>)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub enum " + name +
      TypeParam.ToStringMultiple(typeParams, ind)
      + " {" +
      SeqToString(
        variants,
        (variant: EnumCase) =>
          "\n" + ind + IND + variant.ToString(ind + IND, false), ",") +
      "\n" + ind + "}"
    }
  }

  type TypeParamConstraint = Type

  datatype TypeParam =
    | RawTypeParam(content: string, constraints: seq<TypeParamConstraint>)
  {
    static function ToStringMultiple(typeParams: seq<TypeParam>, ind: string): string {
      if |typeParams| == 0 then "" else
      "<" + SeqToString(typeParams, (t: TypeParam) => t.ToString(ind + IND), ", ") + ">"
    }
    static function {:tailrecursion true} AddConstraintsMultiple(
      typeParams: seq<TypeParam>, constraints: seq<TypeParamConstraint>
    ): seq<TypeParam> {
      if |typeParams| == 0 then []
      else
        [typeParams[0].AddConstraints(constraints)] + AddConstraintsMultiple(typeParams[1..], constraints)
    }
    function AddConstraints(constraints: seq<TypeParamConstraint>): TypeParam {
      this.(constraints := this.constraints + constraints)
    }
    function ToString(ind: string): string {
      content + (
        if |constraints| == 0 then
          ""
        else
          ": " + SeqToString(constraints, (t: TypeParamConstraint) requires t < this =>
                               t.ToString(ind + IND), " + "))
    }
  }
  const Self := Borrowed(SelfOwned)
  const SelfMut := BorrowedMut(SelfOwned)
  function Rc(underlying: Type): Type {
    TypeApp("::std::rc::Rc", [underlying])
  }
  function RefCell(underlying: Type): Type {
    TypeApp("::std::cell::RefCell", [underlying])
  }
  function Vec(underlying: Type): Type {
    TypeApp("::std::vec::Vec", [underlying])
  }
  function NewVec(elements: seq<Expr>): Expr {
    Call(RawExpr("vec!"), [], elements)
  }
  
  const CloneTrait := RawType("Clone")
  const DafnyPrintTrait := RawType("::dafny_runtime::DafnyPrint")
  const DefaultTrait := RawType("::std::default::Default")
  const StaticTrait := RawType("'static")

  function RawType(content: string): Type {
    TypeApp(content, [])
  }

  datatype Type =
    | SelfOwned
    | U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128
    | TypeApp(baseName: string, arguments: seq<Type>)
    | Borrowed(underlying: Type)
    | BorrowedMut(underlying: Type)
    | ImplType(underlying: Type)
    | DynType(underlying: Type)
    | TupleType(arguments: seq<Type>)
    | FnType(arguments: seq<Type>, returnType: Type)
    | IntersectionType(left: Type, right: Type)
  {
    function ToString(ind: string): string {
      match this {
        case Borrowed(underlying) => "&" + underlying.ToString(ind)
        case BorrowedMut(underlying) => "&mut " + underlying.ToString(ind)
        case ImplType(underlying) => "impl " + underlying.ToString(ind)
        case DynType(underlying) => "dyn " + underlying.ToString(ind)
        case FnType(arguments, returnType) => 
          "::std::ops::Fn("+
            SeqToString(arguments, (arg: Type) requires arg < this =>
              arg.ToString(ind + IND), ", ")
          +") -> " + returnType.ToString(ind + IND)
        case IntersectionType(left, right) =>
          left.ToString(ind) + " + " + right.ToString(ind)
        case TupleType(args) =>
          (if args == [] then
            "()"
           else
            "(" +
            SeqToString(args, (arg: Type) requires arg < this => arg.ToString(ind + IND), ", ")
            + ")")
        case TypeApp(base, args) =>
          base +
          (if args == [] then
            ""
           else
            "<" +
            SeqToString(args, (arg: Type) requires arg < this => arg.ToString(ind + IND), ", ")
            + ">")
            
        case SelfOwned() => "Self"
        case U8() => "u8"
        case U16() => "u16"
        case U32() => "u32"
        case U64() => "u64"
        case U128() => "u128"
        case I8() => "i8"
        case I16() => "i16"
        case I32() => "i32"
        case I64() => "i64"
        case I128() => "i128"
      }
    }
  }

  datatype Trait =
    | Trait(typeParams: seq<TypeParam>, tpe: Type, where: string, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      "trait " + TypeParam.ToStringMultiple(typeParams, ind) + tpe.ToString(ind)
      + (if where != "" then "\n" + ind + IND + where else "")
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }

  datatype Impl =
    | ImplFor(typeParams: seq<TypeParam>, tpe: Type, forType: Type, where: string, body: seq<ImplMember>)
    | Impl(typeParams: seq<TypeParam>, tpe: Type, where: string, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      "impl " + TypeParam.ToStringMultiple(typeParams, ind) + tpe.ToString(ind)
      + (if ImplFor? then " for " + forType.ToString(ind + IND) else "")
      + (if where != "" then "\n" + ind + IND + where else "")
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }
  datatype ImplMember =
    | RawImplMember(content: string)
    | FnDecl(pub: VISIBILITY, fun: Fn)
  {
    function ToString(ind: string): string {
      if FnDecl? then
        (if pub == PUB then "pub " else "") + fun.ToString(ind)
      else assert RawImplMember?; content
    }
  }
  newtype VISIBILITY = x: int | 0 <= x < 2
  const PUB := 1 as VISIBILITY
  const PRIV := 0 as VISIBILITY

  datatype Formal =
    Formal(name: string, tpe: Type)
  {
    function ToString(ind: string): string {
      if name == "self" && tpe.SelfOwned? then name
      else if name == "&self" && tpe == Borrowed(SelfOwned) then name
      else if name == "&mut self" && tpe == Borrowed(SelfMut) then name
      else
        name + ": " + tpe.ToString(ind)
    }
    static const self := Formal("&self", Self)
    static const selfOwned := Formal("self", SelfOwned)
    static const selfMut := Formal("&mut self", SelfMut)
  }

  datatype Pattern =
    RawPattern(content: string)
  {
    function ToString(ind: string): string {
      content
    }
  }

  datatype MatchCase =
    MatchCase(pattern: Pattern, rhs: Expr)
  {
    function Height(): nat {
      1 + rhs.Height()
    }
    function ToString(ind: string): string
      decreases Height()
    {
      var newIndent := if rhs.Block? then ind else ind + IND;
      var rhsString := rhs.ToString(newIndent);

      pattern.ToString(ind) + " =>" +
      if '\n' in rhsString && rhsString[0] != '{' then "\n" + ind + IND + rhsString
      else " " + rhsString
    }
  }

  datatype AssignIdentifier =
    AssignIdentifier(identifier: string, rhs: Expr)
  {
    function Height(): nat {
      1 + rhs.Height()
    }

    function ToString(ind: string): string
      decreases Height()
    {
      identifier + ": " + rhs.ToString(ind + IND)
    }
  }

  // When a raw stream is given, try to put some indentation on it
  function AddIndent(raw: string, ind: string): string {
    if |raw| == 0 then raw
    else if raw[0] in "[({" then
      [raw[0]] + AddIndent(raw[1..], ind + IND)
    else if raw[0] in "})]" && |ind| > 2 then
      [raw[0]] + AddIndent(raw[1..], ind[..|ind|-2])
    else if raw[0] == '\n' then
      [raw[0]] + ind + AddIndent(raw[1..], ind)
    else
      [raw[0]] + AddIndent(raw[1..], ind)
  }

  function max(i: nat, j: nat): nat {
    if i < j then j else i
  }

  datatype DeclareType = MUT | CONST

  function RcNew(underlying: Expr): Expr {
    Call(RawExpr("::std::rc::Rc::new"), [], [underlying])
  }

  datatype Associativity = LeftToRight | RightToLeft | RequiresParentheses
  datatype PrintingInfo = 
    | Precedence(precedence: nat)
    | SuffixPrecedence(precedence: nat)
    | PrecedenceAssociativity(precedence: nat, associativity: Associativity)

  datatype Expr =
      RawExpr(content: string)
    | Match(matchee: Expr, cases: seq<MatchCase>)
    | StmtExpr(stmt: Expr, rhs: Expr)
    | Block(underlying: Expr)
    | StructBuild(name: string, assignments: seq<AssignIdentifier>)
    | Tuple(arguments: seq<Expr>)
    | UnaryOp(op1: string, underlying: Expr, format: Format.UnOpFormat)
    | BinaryOp(op2: string, left: Expr, right: Expr, format2: Format.BinOpFormat)
    | LiteralInt(value: string)
    | ConversionNum(tpe: Type, underlying: Expr)
    | DeclareVar(declareType: DeclareType, name: string, optType: Option<Type>, optRhs: Option<Expr>)
    | AssignVar(name: string, rhs: Expr)
    | IfExpr(cond: Expr, thn: Expr, els: Expr)
    | Loop(optCond: Option<Expr>, underlying: Expr)
    | For(name: string, range: Expr, body: Expr)
    | Labelled(lbl: string, underlying: Expr)
    | Break(optLbl: Option<string>)
    | Continue(optLbl: Option<string>)
    | Return(optExpr: Option<Expr>)
    | Call(obj: Expr, typeParameters: seq<Type>, arguments: seq<Expr>)
    | Select(obj: Expr, name: string)
    | Borrow(underlying: Expr)
  {
    predicate NoExtraSemicolonAfter() {
      DeclareVar? || AssignVar? || Break? || Continue? || Return? || 
        (RawExpr? && |content| > 0 && content[|content| - 1] == ';')
    }
    // Taken from https://doc.rust-lang.org/reference/expressions.html
    const printingInfo: PrintingInfo := 
      match this {
        case RawExpr(_) => Precedence(200)
        // Paths => Precedence(1)
        // Method call => Precedence(2)
        // Field expression => PrecedenceAssociativity(3, LeftToRight)
        // case function call | ArrayIndexing => Precedence(4)
        case UnaryOp(op, underlying, format) =>
          match op {
            case "?" => SuffixPrecedence(5)
            case "-" | "*" | "!" | "&" | "&mut" => Precedence(6)
            case _ => Precedence(200)
          }
        case BinaryOp(op2, left, right, format) =>
          match op2 {
            case "as" => PrecedenceAssociativity(10, LeftToRight)
            case "*" | "/" | "%" => PrecedenceAssociativity(20, LeftToRight)
            case "+" | "-" => PrecedenceAssociativity(30, LeftToRight)
            case "<<" | ">>" => PrecedenceAssociativity(40, LeftToRight)
            case "&" => PrecedenceAssociativity(50, LeftToRight)
            case "^" => PrecedenceAssociativity(60, LeftToRight)
            case "|" => PrecedenceAssociativity(70, LeftToRight)
            case "==" | "!=" | "<" | ">" | "<=" | ">=" => PrecedenceAssociativity(80, RequiresParentheses)
            case "&&" => PrecedenceAssociativity(90, LeftToRight)
            case "||" => PrecedenceAssociativity(100, LeftToRight)
            case ".." | "..=" => PrecedenceAssociativity(110, RequiresParentheses)
            case "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" =>
              PrecedenceAssociativity(110, RightToLeft)
            case _ => PrecedenceAssociativity(0, RequiresParentheses)
          }
          case _ => Precedence(200)
      }

    function Height(): nat {
      match this {
        case LiteralInt(_) => 1
        case ConversionNum(_, underlying) => 1 + underlying.Height()
        case Match(matchee, cases) =>
          1 + max(matchee.Height(),
                  SeqToHeight(cases, (oneCase: MatchCase)
                              requires oneCase < this
                              => oneCase.Height()))
        case StmtExpr(stmt, rhs) =>
          var default := 1 + max(stmt.Height(), rhs.Height());
          match this {
            case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(AssignVar(name2, rhs), last)) =>
              if name == name2 then
                1 + default
              else default
            case _ => default
          }
          
        case Block(underlying) =>
          1 + underlying.Height()
        case StructBuild(name, assignments) =>
          1 + SeqToHeight(assignments, (assignment: AssignIdentifier)
                          requires assignment < this
                          => assignment.Height())
        case Tuple(arguments) =>
          1 + SeqToHeight(arguments, (argument: Expr)
                          requires argument < this
                          => argument.Height())
        // Special cases
        case UnaryOp(_, underlying, _) => 1 + underlying.Height()

        case BinaryOp(op, left, right, format) =>
          1 + max(left.Height(), right.Height())
        case IfExpr(cond, thn, els) =>
          1 + max(cond.Height(), max(thn.Height(), els.Height()))
        case DeclareVar(declareType, name, tpe, expr) =>
          1 + (match expr {
            case Some(e) => e.Height()
            case None => 0
          })
        case AssignVar(name, expr) =>
          1 + expr.Height()
        case Loop(optCond, underlying) =>
          1 + if optCond.Some? then max(optCond.value.Height(), underlying.Height()) else underlying.Height()
        case Labelled(lbl, underlying) =>
          1 + underlying.Height()
        case Break(_) => 1
        case Continue(_) => 1
        case For(name, range, body) =>
          1 + max(range.Height(), body.Height())
        case Return(optExpr) =>
          if optExpr.Some? then 1 + optExpr.value.Height() else 1
        case Call(obj, tpes, args) =>
          1 + max(obj.Height(),
                max(SeqToHeight(tpes, (tpe: Type) requires tpe < this => 1),
                  SeqToHeight(args, (arg: Expr) requires arg < this => arg.Height())))
        case Borrow(underlying) =>
          1 + underlying.Height()
        case Select(expression, name) =>
          1 + expression.Height()
        case _ =>
          assert RawExpr?;
          1
      }
    }

    // Wish: Prove that Optimize() preserves semantics, if any
    opaque function Optimize(): (r: Expr)
      ensures this == r || r.Height() < this.Height()
    {
      match this {
         // Special cases
        case UnaryOp("!", BinaryOp("==", left, right, format),
          CombineNotInner()) =>
          assert BinaryOp("==", left, right, format).Height()
              == BinaryOp("!=", left, right, BinOpFormat.NoFormat()).Height();
          BinaryOp("!=", left, right, BinOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, NoFormat()),
          CombineNotInner()) =>
          assert BinaryOp(">=", left, right, BinOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinOpFormat.NoFormat()).Height();
          BinaryOp(">=", left, right, BinOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, ReverseOperands()),
          CombineNotInner()) =>
          assert BinaryOp("<=", right, left, BinOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinOpFormat.ReverseOperands()).Height();
          BinaryOp("<=", right, left, BinOpFormat.NoFormat())

        case ConversionNum(tpe, expr) =>
          if || tpe.U8? || tpe.U16? || tpe.U32? || tpe.U64? || tpe.U128?
             || tpe.I8? || tpe.I16? || tpe.I32? || tpe.I64? || tpe.I128? then
            match expr {
              case LiteralInt(number) =>
                RawExpr(number)
              case _ => this
            }
          else
            this
        case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(AssignVar(name2, rhs), last)) =>
          if name == name2 then
            var rewriting := StmtExpr(DeclareVar(mod, name, Some(tpe), Some(rhs)), last);
            assert rewriting.Height() < this.Height() by {
              assert StmtExpr(AssignVar(name2, rhs), last).Height() ==
                1 + max(AssignVar(name2, rhs).Height(), last.Height()) ==
                1 + max(1 + rhs.Height(), last.Height());
              assert this.Height() == 2 + max(1, 1 + max(1 + rhs.Height(), last.Height()));
              assert rewriting.Height() == 1 + max(1 + rhs.Height(), last.Height());
            }
            rewriting
          else
            this
        case _ => this
      }
    }

    predicate LeftRequiresParentheses(left: Expr) {
      printingInfo.precedence <= left.printingInfo.precedence &&
      (printingInfo.precedence == left.printingInfo.precedence ==>
        (printingInfo.PrecedenceAssociativity? &&
        !printingInfo.associativity.LeftToRight?))
    }

    predicate RightRequiresParentheses(right: Expr) {
      printingInfo.precedence <= right.printingInfo.precedence &&
      (printingInfo.precedence == right.printingInfo.precedence ==>
        (printingInfo.PrecedenceAssociativity? &&
         !printingInfo.associativity.RightToLeft?))
    }

    function ToString(ind: string): string
      decreases Height()
    {
      match this.Optimize() {
        case LiteralInt(number) =>
          "::std::rc::Rc::new(::dafny_runtime::BigInt::parse_bytes(b\"" + number + "\", 10).unwrap())"
        case ConversionNum(tpe, expr) =>
          if || tpe.U8? || tpe.U16? || tpe.U32? || tpe.U64? || tpe.U128?
             || tpe.I8? || tpe.I16? || tpe.I32? || tpe.I64? || tpe.I128? then
            "num::ToPrimitive::to_"+tpe.ToString(ind)+"(" + expr.ToString(ind) + ").unwrap()"
          else
            "<b>Unsupported: Numeric conversion to " + tpe.ToString(ind) + "</b>"
        case Match(matchee, cases) =>
          "match " + matchee.ToString(ind + IND) + " {" +
          SeqToString(cases,
                      (c: MatchCase) requires c.Height() < this.Height() =>
                        "\n" + ind + IND + c.ToString(ind + IND), ",") +
          "\n" + ind + "}"
        case StmtExpr(stmt, rhs) => // They are built like StmtExpr(StmtExpr(StmtExpr(..., 1), 2), 3...)
          if stmt == RawExpr("") then rhs.ToString(ind) else
          stmt.ToString(ind) + (if stmt.NoExtraSemicolonAfter() then "" else ";") +
          "\n" + ind + rhs.ToString(ind)
        case Block(underlying) =>
          "{\n" + ind + IND + underlying.ToString(ind + IND) + "\n" + ind + "}"
        case IfExpr(cond, thn, els) =>
          "if " + cond.ToString(ind + IND) + " {\n" + ind + IND + thn.ToString(ind + IND) +
          "\n" + ind + "} else {\n" + ind + IND + els.ToString(ind + IND) + "\n" + ind + "}"
        case StructBuild(name, assignments) =>
          name + " {" +
          SeqToString(assignments, (assignment: AssignIdentifier)
                      requires assignment.Height() < this.Height()
                      =>
                        "\n" + ind + IND + assignment.ToString(ind + IND), ",") +
          (if |assignments| > 0 then "\n" + ind else "") + "}"
        case Tuple(arguments) =>
          "(" +
          SeqToString(arguments, (arg: Expr)
                      requires arg.Height() < this.Height()
                      =>
                        "\n" + ind + IND + arg.ToString(ind + IND), ",") +
          (if |arguments| > 0 then "\n" + ind else "") + ")"

        case UnaryOp(op, underlying, format) =>
          var (leftP, rightP) :=
            if printingInfo.precedence < underlying.printingInfo.precedence then
              ("(", ")")
            else
              ("", "");
          var leftOp := if op == "&mut" then op + " " else if op == "?" then "" else op;
          var rightOp := if op == "?" then op else "";

          leftOp + leftP  + underlying.ToString(ind) + rightP + rightOp
        case BinaryOp(op2, left, right, format) =>
          var (leftLeftP, leftRighP) :=
            if LeftRequiresParentheses(left) then ("(", ")") else ("", "");
          var (rightLeftP, rightRightP) :=
            if RightRequiresParentheses(right) then ("(", ")") else ("", "");
          var opRendered := if op2 == "as" then " " + op2 + " " else op2;
          var indLeft := if leftLeftP == "(" then ind + IND else ind;
          var indRight := if rightLeftP == "(" then ind + IND else ind;
          leftLeftP + left.ToString(indLeft) + leftRighP + opRendered + rightLeftP + right.ToString(indRight) + rightRightP
        case DeclareVar(declareType, name, optType, optExpr) =>
          "let " + (if declareType == MUT then "mut " else "") +
          name + (if optType.Some? then ": " + optType.value.ToString(ind + IND) else "") +
          (if optExpr.Some? then " = " + optExpr.value.ToString(ind + IND) else "") + ";"
        case AssignVar(name, expr) =>
          name + " = " + expr.ToString(ind + IND) + ";"
        case Labelled(name, underlying) =>
          "'" + name + ": " + underlying.ToString(ind)
        case Break(optLbl) =>
          match optLbl {
            case Some(lbl) => "break '" + lbl + ";"
            case None => "break;"
          }
        case Continue(optLbl) =>
          match optLbl {
            case Some(lbl) => "continue '" + lbl + ";"
            case None => "continue;"
          }
        case Loop(optCond, underlying) =>
          (match optCond {
            case None => "loop"
            case Some(c) => "while " + c.ToString(ind + IND)
          }) + " {\n" + ind + IND + underlying.ToString(ind + IND) + "\n" + ind + "}"
        case For(name, range, body) =>
          "for "+ name +" in " + range.ToString(ind + IND) + " {\n" + ind + IND +
          body.ToString(ind + IND) + "\n" + ind + "}"
        case Return(optExpr) =>
          "return" + (if optExpr.Some? then " " + optExpr.value.ToString(ind + IND) else "") + ";"
        case Call(expr, tpes, args) =>
          expr.ToString(ind) + (
            if |tpes| == 0 then ""
            else
              "::<" + SeqToString(tpes, (tpe: Type) => tpe.ToString(ind + IND), ", ") +">"
          ) + "("+SeqToString(args, (arg: Expr) requires arg.Height() < this.Height() => arg.ToString(ind + IND), ", ")+")"
        case Borrow(underlying) =>
          "&(" + underlying.ToString(ind) + ")"
        case Select(expression, name) =>
          "("+expression.ToString(ind)+")." + name        
        case r =>
          assert r.RawExpr?; AddIndent(r.content, ind)
      }
    }
    function Then(rhs2: Expr): Expr {
      if this.StmtExpr? then
        StmtExpr(stmt, rhs.Then(rhs2))
      else
        StmtExpr(this, rhs2)
    }
  }

  datatype Fn =
    Fn(name: string, typeParams: seq<TypeParam>, formals: seq<Formal>,
       returnType: Option<Type>,
       where: string,
       body: Option<Expr>)
  {
    function ToString(ind: string): string {
      "fn " + name + TypeParam.ToStringMultiple(typeParams, ind) +
      "(" + SeqToString(formals, (formal: Formal) => formal.ToString(ind), ", ") + ")" +
      (match returnType case Some(t) => " -> " + t.ToString(ind) case _ => "") +
      (if where == "" then "" else "\n" + ind + IND + where) +
      match body {
        case None => ";"
        case Some(body) =>
          " {\n" + ind + IND +
          body.ToString(ind + IND) +
          "\n" + ind + "}"
      }
    }
  }
}

module {:extern "DCOMP"} DCOMP {
  import opened DAST
  import Strings = Std.Strings
  import Std
  import opened Std.Wrappers
  import R = RAST
  const IND := R.IND
  type Type = DAST.Type
  type Formal = DAST.Formal

  // List taken from https://doc.rust-lang.org/book/appendix-01-keywords.html
  const reserved_rust := {
    "as","async","await","break","const","continue",
    "crate","dyn","else","enum","extern","false","fn","for","if","impl",
    "in","let","loop","match","mod","move","mut","pub","ref","return",
    "Self","self","static","struct","super","trait","true","type","union",
    "unsafe","use","where","while","Keywords","The","abstract","become",
    "box","do","final","macro","override","priv","try","typeof","unsized",
    "virtual","yield"}

  predicate is_tuple_numeric(i: string) {
    |i| >= 2 && i[0] == '_' &&
    i[1] in "0123456789" &&
    (|i| == 2 ||
     (|i| == 3 && i[2] in "0123456789"))
  }

  predicate has_special(i: string) {
    if |i| == 0 then false
    else if i[0] == '.' then true
    else if i[0] == '#' then true // otherwise "escapeIdent("r#") becomes "r#""
    else if i[0] == '_' then
      if 2 <= |i| then
        if i[1] != '_' then true
        else has_special(i[2..])
      else
        true
    else
      has_special(i[1..])
  }

  function idiomatic_rust(i: string): string
    requires !has_special(i)
  {
    if |i| == 0 then ""
    else if i[0] == '_' then
      assert 2 <= |i| && i[1] == '_';
      "_" + idiomatic_rust(i[2..])
    else
      [i[0]] + idiomatic_rust(i[1..])
  }

  function replaceDots(i: string): string {
    if |i| == 0 then
      ""
    else if i[0] == '.' then
      "_d" + replaceDots(i[1..])
    else
      [i[0]] + replaceDots(i[1..])
  }

  predicate is_tuple_builder(i: string) {
    && |i| >= 9
    && i[..8] == "___hMake"
    && i[8] in "0123456789"
    && (|i| == 9 || (|i| == 10 && i[9] in "0123456789"))
  }

  function better_tuple_builder_name(i: string): string
    requires is_tuple_builder(i)
  {
    "_T" + i[8..]
  }

  predicate is_dafny_generated_id(i: string) {
    && |i| > 0 && i[0] == '_' && !has_special(i[1..])
    && (|i| >= 2 ==> i[1] != 'T') // To avoid conflict with tuple builders _T<digits>
  }

  predicate is_idiomatic_rust(i: string) {
    0 < |i| && !has_special(i) && i !in reserved_rust
  }

  function escapeIdent(i: string): string {
    if is_tuple_numeric(i) then
      i
    else if is_tuple_builder(i) then
      better_tuple_builder_name(i)
    else if i in reserved_rust then
      "r#" + i
    else if is_idiomatic_rust(i) then
      idiomatic_rust(i)
    else if is_dafny_generated_id(i) then
      i // Dafny-generated identifiers like "_module", cannot be written in Dafny itself
    else
      var r := replaceDots(i);
      "r#_" + r
  }

  class COMP {
    static method GenModule(mod: Module, containingPath: seq<Ident>) returns (s: R.Mod) {
      var body := GenModuleBody(mod.body, containingPath + [Ident.Ident(mod.name)]);

      s := if mod.isExtern then
        R.ExternMod(escapeIdent(mod.name))
      else
        R.Mod(escapeIdent(mod.name), body);
    }

    static method GenModuleBody(body: seq<ModuleItem>, containingPath: seq<Ident>) returns (s: seq<R.ModDecl>) {
      s := [];
      var i := 0;
      while i < |body| {
        var generated;
        match body[i] {
          case Module(m) =>
            var mm := GenModule(m, containingPath);
            generated := [R.ModDecl(mm)];
          case Class(c) =>
            generated := GenClass(c, containingPath + [Ident.Ident(c.name)]);
          case Trait(t) =>
            var tt := GenTrait(t, containingPath);
            generated := [R.RawDecl(tt)];
          case Newtype(n) =>
            generated := GenNewtype(n);
          case Datatype(d) =>
            generated := GenDatatype(d);
        }
        s := s + generated;
        i := i + 1;
      }
    }

    static method GenTypeParameters(params: seq<Type>)
      returns (
        typeParamsSet: set<Type>,
        typeParams: seq<R.TypeParam>,
        constrainedTypeParams: seq<R.TypeParam>,
        whereConstraints: string)
    {
      typeParamsSet := {};
      typeParams := [];
      constrainedTypeParams := [];
      whereConstraints := "";
      var tpI := 0;

      if |params| > 0 {
        while tpI < |params| {
          var tp := params[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + [R.RawTypeParam(genTp.ToString(IND), [])];
          tpI := tpI + 1;
        }
      }
      var baseConstraints := [R.CloneTrait, R.DafnyPrintTrait, R.StaticTrait];
      constrainedTypeParams := R.TypeParam.AddConstraintsMultiple(
        typeParams, baseConstraints
      );
    }

    static method GenClass(c: Class, path: seq<Ident>) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, R.IND + R.IND);

      var fields: seq<R.Formal> := [];
      var fieldInits: seq<R.AssignIdentifier> := [];
      var fieldI := 0;
      while fieldI < |c.fields| {
        var field := c.fields[fieldI];
        var fieldType := GenType(field.formal.typ, false, false);
        fields := fields + [R.Formal("pub " + escapeIdent(field.formal.name), R.TypeApp("::std::cell::RefCell", [fieldType]))];

        match field.defaultValue {
          case Some(e) => {
            var eStr, _, _ := GenExpr(e, None, [], true);
            fieldInits := fieldInits + [
              R.AssignIdentifier(
                escapeIdent(field.formal.name),
                R.RawExpr("::std::cell::RefCell::new(" + eStr.ToString(IND) + ")"))];
          }
          case None => {
            fieldInits := fieldInits + [
              R.AssignIdentifier(
                escapeIdent(field.formal.name),
                R.RawExpr("::std::cell::RefCell::new(::std::default::Default::default())"))];
          }
        }

        fieldI := fieldI + 1;
      }

      var typeParamI := 0;
      while typeParamI < |c.typeParams| {
        var tpeGen := GenType(c.typeParams[typeParamI], false, false);
        fields := fields + [R.Formal("_phantom_type_param_" + Strings.OfNat(typeParamI), R.TypeApp("::std::marker::PhantomData", [tpeGen]))];
        fieldInits := fieldInits + [
          R.AssignIdentifier(
            "_phantom_type_param_" + Strings.OfNat(typeParamI),
            R.RawExpr("::std::marker::PhantomData"))];

        typeParamI := typeParamI + 1;
      }

      var struct := R.Struct([], escapeIdent(c.name), sTypeParams, R.NamedFormals(fields));
      var typeParamsAsTypes := 
        Std.Collections.Seq.Map((typeParam: R.TypeParam) => R.RawType(typeParam.content), sTypeParams);

      s := [R.StructDecl(struct)];

      var implBodyRaw, traitBodies := GenClassImplBody(c.body, false, Type.Path([], [], ResolvedType.Datatype(path)), typeParamsSet);
      var implBody :=
        [R.FnDecl(
           R.PUB,
           R.Fn(
             "new",
             [], [], Some(R.SelfOwned),
             "",
             Some(R.StructBuild(
                    escapeIdent(c.name),
                    fieldInits
                  ))
           ))] + implBodyRaw;

      var i := R.Impl(
        sConstrainedTypeParams,
        R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
        whereConstraints,
        implBody
      );
      s := s + [R.ImplDecl(i)];
      if (|c.superClasses| > 0) {
        var i := 0;
        while i < |c.superClasses| {
          var superClass := c.superClasses[i];
          match superClass {
            case Path(traitPath, typeArgs, Trait(_)) => {
              var pathStr := GenPath(traitPath);
              var typeArgs := GenTypeArgs(typeArgs, false, false);
              var body: seq<R.ImplMember> := [];
              if traitPath in traitBodies {
                body := traitBodies[traitPath];
              }

              var genSelfPath := GenPath(path);
              var x := R.ImplDecl(
                R.ImplFor(
                  sConstrainedTypeParams,
                  R.TypeApp(pathStr, typeArgs),
                  R.Rc(R.TypeApp(genSelfPath, typeParamsAsTypes)),
                  whereConstraints,
                  body
                ));
              s := s + [x];
            }
            case _ => {}
          }
          i := i + 1;
        }
      }

      var d := R.ImplFor(
        sConstrainedTypeParams,
        R.DefaultTrait,
        R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
        whereConstraints,
        [R.FnDecl(
           R.PRIV,
           R.Fn(
             "default", [], [], Some(R.SelfOwned),
             "",
             Some(R.RawExpr(escapeIdent(c.name) + "::new()"))))]
      );
      var defaultImpl := [R.ImplDecl(d)];

      var p :=
        R.ImplFor(
          sConstrainedTypeParams,
          R.DafnyPrintTrait,
          R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
          "",
          [R.FnDecl(
             R.PRIV,
             R.Fn(
               "fmt_print", [],
               [R.Formal.self, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("_in_seq", R.RawType("bool"))],
               Some(R.RawType("std::fmt::Result")),
               "",
               Some(R.RawExpr("write!(_formatter, \"" + c.enclosingModule.id + "." + c.name + "\")"))
             ))]
        );
      var printImpl := [R.ImplDecl(p)];

      var pp := R.ImplFor(
        sTypeParams,
        R.RawType("::std::cmp::PartialEq"),
        R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
        "",
        [R.FnDecl(
           R.PRIV,
           R.Fn(
             "eq", [],
             [R.Formal.self, R.Formal("other", R.Self)],
             Some(R.RawType("bool")),
             "",
             Some(R.RawExpr("::std::ptr::eq(self, other)"))
           ))]
      );
      var ptrPartialEqImpl := [R.ImplDecl(pp)];

      s := s + defaultImpl + printImpl + ptrPartialEqImpl;
    }

    static method GenTrait(t: Trait, containingPath: seq<Ident>) returns (s: string) {
      var typeParamsSet := {};
      var typeParams := [];
      var tpI := 0;
      if |t.typeParams| > 0 {
        while tpI < |t.typeParams| {
          var tp := t.typeParams[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + [genTp];
          tpI := tpI + 1;
        }
      }

      var fullPath := containingPath + [Ident.Ident(t.name)];
      var implBody, _ := GenClassImplBody(t.body, true, Type.Path(fullPath, [], ResolvedType.Trait(fullPath)), typeParamsSet);
      s :=
        R.TraitDecl(R.Trait(
                      [], R.TypeApp(escapeIdent(t.name), typeParams),
                      "",
                      implBody
                    )).ToString(IND);
    }

    static method GenNewtype(c: Newtype) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var typeParamsAsTypes := 
        Std.Collections.Seq.Map((t: R.TypeParam) => R.RawType(t.content), sTypeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, R.IND + R.IND);

      var underlyingType;
      match NewtypeToRustType(c.base, c.range) {
        case Some(v) =>
          underlyingType := v;
        case None =>
          underlyingType := GenType(c.base, false, false);
      }
      s := [
        R.StructDecl(
          R.Struct(
            [
              R.RawAttribute("#[derive(Clone, PartialEq)]"),
              R.RawAttribute("#[repr(transparent)]")
            ],
            escapeIdent(c.name),
            sTypeParams,
            R.NamelessFormals([R.NamelessFormal(R.PUB, underlyingType)])
          ))];

      var fnBody := "";

      match c.witnessExpr {
        case Some(e) => {
          // TODO(shadaj): generate statements
          var eStr, _, _ := GenExpr(e, None, [], true);
          fnBody := fnBody + escapeIdent(c.name) + "(" + eStr.ToString(IND) + ")\n";
        }
        case None => {
          fnBody := fnBody + escapeIdent(c.name) + "(::std::default::Default::default())";
        }
      }

      var body :=
        R.FnDecl(
          R.PRIV,
          R.Fn(
            "default", [], [], Some(R.SelfOwned),
            "",
            Some(R.RawExpr(fnBody))
          ));
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            sConstrainedTypeParams,
            R.DefaultTrait,
            R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
            whereConstraints,
            [body]))];
      s := s + [
        R.ImplDecl(R.ImplFor(
                     sConstrainedTypeParams,
                     R.DafnyPrintTrait,
                     R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
                     "",
                     [R.FnDecl(R.PRIV,
                               R.Fn("fmt_print", [],
                                    [R.Formal.self, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("in_seq", R.RawType("bool"))],
                                    Some(R.RawType("::std::fmt::Result")),
                                    "",
                                    Some(R.RawExpr("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))
                               ))]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            sConstrainedTypeParams,
            R.RawType("::std::ops::Deref"),
            R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
            "",
            [R.RawImplMember("type Target = " + underlyingType.ToString(IND) + ";"),
             R.FnDecl(
               R.PRIV,
               R.Fn("deref", [],
                    [R.Formal.self], Some(R.RawType("&Self::Target")),
                    "",
                    Some(R.RawExpr("&self.0"))))]))];
    }

    static method GenDatatype(c: Datatype) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var typeParamsAsTypes := 
        Std.Collections.Seq.Map((t: R.TypeParam) => R.RawType(t.content), sTypeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, IND + IND);

      var ctors: seq<R.EnumCase> := [];
      var i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorArgs: seq<R.Formal> := [];
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          var formalType := GenType(formal.typ, false, false);
          if c.isCo {
            ctorArgs := ctorArgs + [
              R.Formal(escapeIdent(formal.name),
              R.TypeApp("::dafny_runtime::LazyFieldWrapper", [formalType]))];
          } else {
            ctorArgs := ctorArgs + [
              R.Formal(escapeIdent(formal.name), formalType)];
          }
          j := j + 1;
        }
        ctors := ctors + [R.EnumCase(escapeIdent(ctor.name), R.NamedFormals(ctorArgs))];
        i := i + 1;
      }

      var selfPath := [Ident.Ident(c.name)];
      var implBodyRaw, traitBodies := GenClassImplBody(c.body, false, Type.Path([], [], ResolvedType.Datatype(selfPath)), typeParamsSet);
      var implBody: seq<R.ImplMember> := implBodyRaw;
      i := 0;
      var emittedFields: set<string> := {};
      while i < |c.ctors| {
        // we know that across all ctors, each any fields with the same name have the same type
        // so we want to emit methods for each field that pull the appropriate value given
        // the current variant (and panic if we have a variant with no such field)
        var ctor := c.ctors[i];
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          if !(formal.name in emittedFields) {
            emittedFields := emittedFields + {formal.name};

            var formalType := GenType(formal.typ, false, false);
            var cases: seq<R.MatchCase> := [];
            var k := 0;
            while k < |c.ctors| {
              var ctor2 := c.ctors[k];

              var pattern := escapeIdent(c.name) + "::" + escapeIdent(ctor2.name) + " { ";
              var rhs: string;
              var l := 0;
              var hasMatchingField := false;
              while l < |ctor2.args| {
                var formal2 := ctor2.args[l];
                if formal.name == formal2.name {
                  hasMatchingField := true;
                }
                pattern := pattern + escapeIdent(formal2.name) + ", ";
                l := l + 1;
              }

              pattern := pattern + "}";

              if hasMatchingField {
                if c.isCo {
                  rhs := "::std::ops::Deref::deref(&" + escapeIdent(formal.name) + ".0)";
                } else {
                  rhs := escapeIdent(formal.name) + "";
                }
              } else {
                rhs := "panic!(\"field does not exist on this variant\")";
              }
              var ctorMatch := R.MatchCase(R.RawPattern(pattern), R.RawExpr(rhs));
              cases := cases + [ctorMatch];
              k := k + 1;
            }

            if |c.typeParams| > 0 {
              cases := cases + [
                R.MatchCase(R.RawPattern(escapeIdent(c.name) + "::_PhantomVariant(..)"), R.RawExpr("panic!()"))
              ];
            }

            var methodBody := R.Match(
              R.RawExpr("self"),
              cases
            );

            implBody := implBody + [
              R.FnDecl(
                R.PUB,
                R.Fn(
                  escapeIdent(formal.name),
                  [], [R.Formal.self], Some(R.Borrowed(formalType)),
                  "",
                  Some(methodBody)
                ))];
          }
          j := j + 1;
        }

        i := i + 1;
      }

      if |c.typeParams| > 0 {
        var typeI := 0;
        var types: seq<R.Type> := [];
        while typeI < |c.typeParams| {
          var genTp := GenType(c.typeParams[typeI], false, false);
          types := types + [R.TypeApp("::std::marker::PhantomData::", [genTp])];
          typeI := typeI + 1;
        }
        ctors := ctors + [R.EnumCase("_PhantomVariant",
                                     R.NamelessFormals(Std.Collections.Seq.Map(
                                      tpe => R.NamelessFormal(R.PRIV, tpe), types))
                          )];
      }

      var enumBody :=
        [R.EnumDecl(
           R.Enum([R.RawAttribute("#[derive(PartialEq)]")],
                  escapeIdent(c.name),
                  sTypeParams,
                  ctors
           )),
         R.ImplDecl(
           R.Impl(
             sConstrainedTypeParams,
             R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
             whereConstraints,
             implBody
           ))];

      i := 0;
      var printImplBodyCases: seq<R.MatchCase> := [];
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorMatch := escapeIdent(ctor.name) + " { ";

        var modulePrefix := if c.enclosingModule.id == "_module" then "" else c.enclosingModule.id + ".";
        var printRhs :=
          R.RawExpr("write!(_formatter, \"" + modulePrefix + c.name + "." + escapeIdent(ctor.name) + (if ctor.hasAnyArgs then "(\")?" else "\")?"));

        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          ctorMatch := ctorMatch + escapeIdent(formal.name) + ", ";

          if (j > 0) {
            printRhs := printRhs.Then(R.RawExpr("write!(_formatter, \", \")?"));
          }
          printRhs := printRhs.Then(R.RawExpr("::dafny_runtime::DafnyPrint::fmt_print(" + escapeIdent(formal.name) + ", _formatter, false)?"));

          j := j + 1;
        }

        ctorMatch := ctorMatch + "}";

        if (ctor.hasAnyArgs) {
          printRhs := printRhs.Then(R.RawExpr("write!(_formatter, \")\")?"));
        }

        printRhs := printRhs.Then(R.RawExpr("Ok(())"));

        printImplBodyCases := printImplBodyCases + [
          R.MatchCase(R.RawPattern(escapeIdent(c.name) + "::" + ctorMatch),
                      R.Block(printRhs))
        ];
        i := i + 1;
      }

      if |c.typeParams| > 0 {
        printImplBodyCases := printImplBodyCases + [
          R.MatchCase(R.RawPattern(escapeIdent(c.name) + "::_PhantomVariant(..)"), R.RawExpr("{panic!()}"))
        ];
      }
      var printImplBody := R.Match(
        R.RawExpr("self"),
        printImplBodyCases);
      var printImpl := [
        R.ImplDecl(
          R.ImplFor(
            sConstrainedTypeParams,
            R.DafnyPrintTrait,
            R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
            "",
            [R.FnDecl(
               R.PRIV,
               R.Fn(
                 "fmt_print", [],
                 [R.Formal.self, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("_in_seq", R.RawType("bool"))],
                 Some(R.RawType("std::fmt::Result")),
                 "",
                 Some(printImplBody)))]
          ))];

      var defaultImpl := [];
      if |c.ctors| > 0 {
        i := 0;
        var structName := escapeIdent(c.name) + "::" + escapeIdent(c.ctors[0].name);
        var structAssignments: seq<R.AssignIdentifier> := [];
        while i < |c.ctors[0].args| {
          var formal := c.ctors[0].args[i];
          structAssignments := structAssignments + [
            R.AssignIdentifier(escapeIdent(formal.name), R.RawExpr("::std::default::Default::default()"))
          ];
          i := i + 1;
        }
        var defaultConstrainedTypeParams := R.TypeParam.AddConstraintsMultiple(
          sTypeParams, [R.DefaultTrait]
        );

        defaultImpl := [
          R.ImplDecl(
            R.ImplFor(
              defaultConstrainedTypeParams,
              R.DefaultTrait,
              R.TypeApp(escapeIdent(c.name), typeParamsAsTypes),
              "",
              [R.FnDecl(
                 R.PRIV,
                 R.Fn("default", [], [], Some(R.SelfOwned),
                      "",
                      Some(R.StructBuild(
                             structName,
                             structAssignments
                           )))
               )]
            ))];
      }

      s := enumBody + printImpl + defaultImpl;
    }

    static method GenPath(p: seq<Ident>) returns (s: string) {
      if |p| == 0 {
        // TODO(shadaj): this special casing is not great
        return "Self";
      } else {
        s := "super::";
        var i := 0;
        while i < |p| {
          if i > 0 {
            s := s + "::";
          }

          s := s + escapeIdent(p[i].id);

          i := i + 1;
        }
      }
    }

    static method GenTypeArgs(args: seq<Type>, inBinding: bool, inFn: bool) returns (s: seq<R.Type>) {
      s := [];
      if |args| > 0 {
        var i := 0;
        while i < |args| {
          var genTp := GenType(args[i], inBinding, inFn);
          s := s + [genTp];
          i := i + 1;
        }
      }
    }

    static method GenType(c: Type, inBinding: bool, inFn: bool) returns (s: R.Type) {
      match c {
        case Path(p, args, resolved) => {
          var t := GenPath(p);
          s := R.TypeApp(t, []);

          var typeArgs := GenTypeArgs(args, inBinding, inFn);
          s := s.(arguments := typeArgs);

          match resolved {
            case Datatype(_) => {
              s := R.Rc(s);
            }
            case Trait(_) => {
              if p == [Ident.Ident("_System"), Ident.Ident("object")] {
                s := R.RawType("::std::rc::Rc<dyn ::std::any::Any>");
              } else {
                if inBinding {
                  // impl trait in bindings is not stable
                  s := R.RawType("_");
                } else {
                  s := R.ImplType(s);
                }
              }
            }
            case Newtype(t, range, erased) => {
              if erased {
                match NewtypeToRustType(t, range) {
                  case Some(v) =>
                    s := v;
                  case None =>
                }
              }
            }
          }
        }
        case Nullable(inner) => {
          var innerExpr := GenType(inner, inBinding, inFn);
          s := R.TypeApp("::std::option::Option", [innerExpr]);
        }
        case Tuple(types) => {
          var args := [];
          var i := 0;
          while i < |types| {
            var generated := GenType(types[i], inBinding, inFn);
            args := args + [generated];
            i := i + 1;
          }
          s := R.TupleType(args);
        }
        case Array(element, dims) => {
          var elem := GenType(element, inBinding, inFn);
          s := elem;
          var i := 0;
          while i < dims {
            s := R.Rc(R.RefCell(R.Vec(s)));
            i := i + 1;
          }
        }
        case Seq(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.Rc(R.TypeApp("::dafny_runtime::Sequence", [elem]));
        }
        case Set(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.Rc(R.TypeApp("::dafny_runtime::Set", [elem]));
        }
        case Multiset(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.Rc(R.TypeApp("::dafny_runtime::Multiset", [elem]));
        }
        case Map(key, value) => {
          var keyType := GenType(key, inBinding, inFn);
          var valueType := GenType(value, inBinding, inFn);
          s := R.Rc(R.TypeApp("::dafny_runtime::Map", [keyType, valueType]));
        }
        case Arrow(args, result) => {
          // we cannot use impl until Rc<Fn> impls Fn
          // if inFn || inBinding {
          //  s := "::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(";
          // } else {
          //   s := "::dafny_runtime::FunctionWrapper<impl ::std::ops::Fn(";
          // }
          var argTypes := [];
          var i := 0;
          while i < |args| {

            var generated := GenType(args[i], inBinding, true);
            argTypes := argTypes + [R.Borrowed(generated)];
            i := i + 1;
          }

          var resultType := GenType(result, inBinding, inFn || inBinding);
          s := R.TypeApp(
            "::dafny_runtime::FunctionWrapper",
            [R.FnType(argTypes, R.IntersectionType(resultType, R.StaticTrait))]);

          // if inFn || inBinding {
          //s := s + ") -> " + resultType + " + 'static>>";
          // } else {
          //   s := s + ") -> " + resultType + " + Clone + 'static>";
          // }
        }
        case TypeArg(Ident(name)) => s := R.RawType(escapeIdent(name));
        case Primitive(p) => {
          match p {
            case Int => s := R.Rc(R.RawType("::dafny_runtime::BigInt"));
            case Real => s := R.Rc(R.RawType("::dafny_runtime::BigRational"));
            case String => s := R.Vec(R.RawType("char"));
            case Bool => s := R.RawType("bool");
            case Char => s := R.RawType("char");
          }
        }
        case Passthrough(v) => s := R.RawType(v);
      }
    }

    static method GenClassImplBody(body: seq<ClassItem>, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>)
      returns (s: seq<R.ImplMember>, traitBodies: map<seq<Ident>, seq<R.ImplMember>>)
    {
      s := [];
      traitBodies := map[];

      var i := 0;
      while i < |body| {
        match body[i] {
          case Method(m) => {
            match m.overridingPath {
              case Some(p) => {
                var existing: seq<R.ImplMember> := [];
                if p in traitBodies {
                  existing := traitBodies[p];
                }

                var genMethod := GenMethod(m, true, enclosingType, enclosingTypeParams);
                existing := existing + [genMethod];

                traitBodies := traitBodies + map[p := existing];
              }
              case None => {
                var generated := GenMethod(m, forTrait, enclosingType, enclosingTypeParams);
                s := s + [generated];
              }
            }
          }
        }
        i := i + 1;
      }
    }

    static method GenParams(params: seq<Formal>) returns (s: seq<R.Formal>) {
      s := [];
      var i := 0;
      while i < |params| {
        var param := params[i];
        var paramType := GenType(param.typ, false, false);
        s := s + [R.Formal(escapeIdent(param.name), R.Borrowed(paramType))];
        i := i + 1;
      }
    }

    static method GenMethod(m: Method, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>) returns (s: R.ImplMember) {
      var params: seq<R.Formal> := GenParams(m.params);
      var paramNames := [];
      var paramI := 0;
      while paramI < |m.params| {
        paramNames := paramNames + [m.params[paramI].name];
        paramI := paramI + 1;
      }

      if (!m.isStatic) {
        if (forTrait) {
          params := [R.Formal.self] + params;
        } else {
          var tpe := GenType(enclosingType, false, false);
          params := [R.Formal("self", R.Borrowed(tpe))] + params;
        }
      }

      // TODO: Use mut instead of a tuple for the API of multiple output parameters
      var retTypeArgs := [];
      //var retType := if |m.outTypes| != 1 then "(" else "";

      var typeI := 0;
      while typeI < |m.outTypes| {
        var typeExpr := GenType(m.outTypes[typeI], false, false);
        retTypeArgs := retTypeArgs + [typeExpr];

        typeI := typeI + 1;
      }

      var visibility := R.PUB;//if forTrait then R.PUB else R.PRIV;
      var fnName := escapeIdent(m.name);

      var typeParamsFiltered := [];
      var typeParamI := 0;
      while typeParamI < |m.typeParams| {
        var typeParam := m.typeParams[typeParamI];
        if !(typeParam in enclosingTypeParams) {
          typeParamsFiltered := typeParamsFiltered + [typeParam];
        }

        typeParamI := typeParamI + 1;
      }

      var whereClauses := "";

      var typeParams: seq<R.TypeParam> := [];

      if (|typeParamsFiltered| > 0) {
        whereClauses := whereClauses + " where ";

        var i := 0;
        while i < |typeParamsFiltered| {

          var typeExpr := GenType(typeParamsFiltered[i], false, false);
          typeParams := typeParams + [
            R.RawTypeParam(typeExpr.ToString(IND),
                           [R.CloneTrait,
                            R.DafnyPrintTrait,
                            R.DefaultTrait,
                            R.StaticTrait])
          ];

          i := i + 1;
        }
      }

      var fBody: Option<R.Expr>;

      if m.hasBody {
        var earlyReturn: R.Expr := R.Return(None);
        match m.outVars {
          case Some(outVars) => {

            var tupleArgs := [];

            var outI := 0;
            while outI < |outVars| {

              var outVar := outVars[outI];
              tupleArgs := tupleArgs + [R.RawExpr(escapeIdent(outVar.id))];

              outI := outI + 1;
            }
            earlyReturn := R.Return(Some(R.Tuple(tupleArgs)));
          }
          case None => {}
        }

        var body, _ := GenStmts(m.body, if m.isStatic then None else Some("self"), paramNames, true, earlyReturn);

        fBody := Some(body);
      } else {
        fBody := None;
      }
      s := R.FnDecl(
        visibility,
        R.Fn(
          fnName,
          typeParams,
          params,
          Some(if |retTypeArgs| == 1 then retTypeArgs[0] else R.TupleType(retTypeArgs)),
          whereClauses,
          fBody
        )
      );
    }

    static method GenStmts(stmts: seq<Statement>, selfIdent: Option<string>, params: seq<string>, isLast: bool, earlyReturn: R.Expr) returns (generated: R.Expr, readIdents: set<string>) {
      generated := R.RawExpr("");
      var declarations := {};
      readIdents := {};
      var i := 0;
      while i < |stmts| {
        var stmt := stmts[i];
        var stmtExpr, recIdents := GenStmt(stmt, selfIdent, params, isLast && (i == |stmts| - 1), earlyReturn);
        readIdents := readIdents + (recIdents - declarations);

        match stmt {
          case DeclareVar(name, _, _) => {
            declarations := declarations + {name};
          }
          case _ => {}
        }
        generated := generated.Then(stmtExpr);

        i := i + 1;
      }
    }

    static method GenAssignLhs(lhs: AssignLhs, rhs: string, selfIdent: Option<string>, params: seq<string>) returns (generated: string, needsIIFE: bool, readIdents: set<string>) {
      match lhs {
        case Ident(Ident(id)) => {
          if id in params {
            generated := "*" + escapeIdent(id);
          } else {
            generated := escapeIdent(id);
          }

          readIdents := {id};
          needsIIFE := false;
        }

        case Select(on, field) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, false);
          generated := "*(" + onExpr.ToString(IND) + "." + field + ".borrow_mut()) = " + rhs + ";";
          readIdents := recIdents;
          needsIIFE := true;
        }

        case Index(on, indices) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, false);
          readIdents := recIdents;

          generated := "{\n";

          var i := 0;
          while i < |indices| {
            var idx, _, recIdentsIdx := GenExpr(indices[i], selfIdent, params, true);

            generated := generated + "let __idx" + Strings.OfNat(i) + " = <usize as ::dafny_runtime::NumCast>::from(" + idx.ToString(IND) + ").unwrap();\n";

            readIdents := readIdents + recIdentsIdx;

            i := i + 1;
          }

          generated := generated + onExpr.ToString(IND) + ".borrow_mut()";
          i := 0;
          while i < |indices| {
            generated := generated + "[__idx" + Strings.OfNat(i) + "]";
            i := i + 1;
          }

          generated := generated + " = " + rhs + ";\n}";
          needsIIFE := true;
        }
      }
    }

    static method GenStmt(stmt: Statement, selfIdent: Option<string>, params: seq<string>, isLast: bool, earlyReturn: R.Expr) returns (generated: R.Expr, readIdents: set<string>) {
      match stmt {
        case DeclareVar(name, typ, Some(expression)) => {
          var typeString := GenType(typ, true, false);
          var expr, _, recIdents := GenExpr(expression, selfIdent, params, true);

          generated := R.DeclareVar(R.MUT, escapeIdent(name), Some(typeString), Some(expr));
          readIdents := recIdents;
        }
        case DeclareVar(name, typ, None) => {
          var typeString := GenType(typ, true, false);
          generated := R.DeclareVar(R.MUT, escapeIdent(name), Some(typeString), None);
          readIdents := {};
        }
        case Assign(lhs, expression) => {
          var lhsGen, needsIIFE, recIdents := GenAssignLhs(lhs, "__rhs", selfIdent, params);
          var exprGen, _, exprIdents := GenExpr(expression, selfIdent, params, true);

          if needsIIFE {
            generated := R.Block(
              R.StmtExpr(
                R.DeclareVar(R.CONST, "__rhs", None, Some(exprGen)),
                R.RawExpr(lhsGen)
              )
            );
          } else {
            generated := R.AssignVar(lhsGen, exprGen);
          }

          readIdents := recIdents + exprIdents;
        }
        case If(cond, thn, els) => {
          var cond, _, recIdents := GenExpr(cond, selfIdent, params, true);
          var condString := cond.ToString(IND);

          readIdents := recIdents;
          var thn, thnIdents := GenStmts(thn, selfIdent, params, isLast, earlyReturn);
          readIdents := readIdents + thnIdents;
          var els, elsIdents := GenStmts(els, selfIdent, params, isLast, earlyReturn);
          readIdents := readIdents + elsIdents;
          generated := R.IfExpr(cond, thn, els);
        }
        case Labeled(lbl, body) => {
          var body, bodyIdents := GenStmts(body, selfIdent, params, isLast, earlyReturn);
          readIdents := bodyIdents;
          generated := R.Labelled("label_" + lbl, R.Loop(None, R.StmtExpr(body, R.Break(None))));
        }
        case While(cond, body) => {
          var cond, _, recIdents := GenExpr(cond, selfIdent, params, true);

          readIdents := recIdents;
          var body, bodyIdents := GenStmts(body, selfIdent, params, false, earlyReturn);
          readIdents := readIdents + bodyIdents;

          generated := R.Loop(Some(cond), body);
        }
        case Foreach(boundName, boundType, over, body) => {
          var over, _, recIdents := GenExpr(over, selfIdent, params, true);

          var boundTypeStr := GenType(boundType, false, false);

          readIdents := recIdents;
          var body, bodyIdents := GenStmts(body, selfIdent, params + [boundName], false, earlyReturn);
          readIdents := readIdents + bodyIdents - {boundName};

          generated := R.For(escapeIdent(boundName), over, body);
        }
        case Break(toLabel) => {
          match toLabel {
            case Some(lbl) => {
              generated := R.Break(Some("label_" + lbl));
            }
            case None => {
              generated := R.Break(None);
            }
          }
          readIdents := {};
        }
        case TailRecursive(body) => {
          // clone the parameters to make them mutable
          generated := R.RawExpr("");

          if selfIdent != None {
            generated := generated.Then(R.DeclareVar(R.MUT, "_this", None, Some(R.RawExpr("self.clone()"))));
          }

          var paramI := 0;
          while paramI < |params| {
            var param := params[paramI];
            generated := generated.Then(R.DeclareVar(R.MUT, escapeIdent(param), None, Some(R.RawExpr(escapeIdent(param) + ".clone()"))));
            paramI := paramI + 1;
          }

          var body, bodyIdents := GenStmts(body, if selfIdent != None then Some("_this") else None, [], false, earlyReturn);
          readIdents := bodyIdents;
          generated := generated.Then(R.Labelled("TAIL_CALL_START", 
            R.Loop(None, body)));
        }
        case JumpTailCallStart() => {
          generated := R.Continue(Some("TAIL_CALL_START"));
          readIdents := {};
        }
        case Call(on, name, typeArgs, args, maybeOutVars) => {
          readIdents := {};

          var typeArgString := "";
          if (|typeArgs| >= 1) {
            var typeI := 0;
            var typeArgsR := [];
            while typeI < |typeArgs| {
              var tpe := GenType(typeArgs[typeI], false, false);
              typeArgsR := typeArgsR + [tpe];

              typeI := typeI + 1;
            }
            typeArgString := R.TypeApp("::", typeArgsR).ToString(IND);
          }

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, isOwned, argIdents := GenExpr(args[i], selfIdent, params, false);
            var argExprString := argExpr.ToString(IND);
            if isOwned {
              argExprString := "&" + argExprString;
            }

            argString := argString + argExprString;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var enclosingExpr, _, enclosingIdents := GenExpr(on, selfIdent, params, false);
          readIdents := readIdents + enclosingIdents;
          var enclosingString := enclosingExpr.ToString(IND);
          match on {
            case Companion(_) => {
              enclosingString := enclosingString + "::";
            }
            case _ => {
              enclosingString := "(" + enclosingString + ").";
            }
          }

          var receiver := "";
          match maybeOutVars {
            case Some(outVars) => {
              if (|outVars| > 1) {
                receiver := "(";
              }
              var outI := 0;
              while outI < |outVars| {
                if outI > 0 {
                  receiver := receiver + ", ";
                }

                var outVar := outVars[outI];
                receiver := receiver + outVar.id;

                outI := outI + 1;
              }
              if (|outVars| > 1) {
                receiver := receiver + ")";
              }
            }
            case None => {}
          }

          var renderedName := match name {
            case Name(name) => escapeIdent(name)
            case MapBuilderAdd() | SetBuilderAdd() => "add"
            case MapBuilderBuild() | SetBuilderBuild() => "build"
          };

          generated := R.RawExpr(
            (if receiver != "" then (receiver + " = ") else "") +
            enclosingString + renderedName + typeArgString + "(" + argString + ");");
        }
        case Return(expr) => {
          var expr, _, recIdents := GenExpr(expr, selfIdent, params, true);
          readIdents := recIdents;

          if isLast {
            generated := expr;
          } else {
            generated := R.Return(Some(expr));
          }
        }
        case EarlyReturn() => {
          generated := earlyReturn;
          readIdents := {};
        }
        case Halt() => {
          generated := R.RawExpr("panic!(\"Halt\");");
          readIdents := {};
        }
        case Print(e) => {
          var printedExpr, isOwned, recIdents := GenExpr(e, selfIdent, params, false);
          var printedExprString := printedExpr.ToString(IND);
          if isOwned {
            printedExprString := "&(" + printedExprString + ")";
          }
          generated := R.RawExpr("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper(" + printedExprString + "));");
          readIdents := recIdents;
        }
      }
    }

    static const OpTable: map<BinOp, string>
    := 
    map[
        Mod() := "%",
        And() := "&&",
        Or() := "||",
        Div() := "/",
        Lt() := "<",
        Plus() := "+",
        Minus() := "-",
        Times() := "*",
        BitwiseAnd() := "&",
        BitwiseOr() := "|",
        BitwiseXor() := "^",
        BitwiseShiftRight() := ">>",
        BitwiseShiftLeft() := "<<"
      ]

    static function NewtypeToRustType(base: Type, range: NewtypeRange)
      : Option<R.Type> {
      match range {
        case NoRange() => None
        case U8() => Some(R.Type.U8)
        case U16() => Some(R.Type.U16)
        case U32() => Some(R.Type.U32)
        case U64() => Some(R.Type.U64)
        case U128() => Some(R.Type.U128)
        case I8() => Some(R.Type.I8)
        case I16() => Some(R.Type.I16)
        case I32() => Some(R.Type.I32)
        case I64() => Some(R.Type.I64)
        case I128() => Some(R.Type.I128)
        case _ => None
      }
    }

    static method GenExpr(e: Expression, selfIdent: Option<string>, params: seq<string>, mustOwn: bool) returns (r: R.Expr, isOwned: bool, readIdents: set<string>)
      ensures mustOwn ==> isOwned
      decreases e {
      match e {
        case Literal(BoolLiteral(false)) => {
          r := R.RawExpr("false");
          isOwned := true;
          readIdents := {};
        }
        case Literal(BoolLiteral(true)) => {
          r := R.RawExpr("true");
          isOwned := true;
          readIdents := {};
        }
        case Literal(IntLiteral(i, t)) => {
          match t {
            case Primitive(Int) => {
              r := R.LiteralInt(i);
            }
            case o => {
              var genType := GenType(o, false, false);
              r := R.RawExpr("(" + i + " as " + genType.ToString(IND) + ")");
            }
          }

          isOwned := true;
          readIdents := {};
        }
        case Literal(DecLiteral(n, d, t)) => {
          match t {
            case Primitive(Real) => {
              r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\"" + n + "\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"" + d + "\", 10).unwrap())"));
            }
            case o => {
              var genType := GenType(o, false, false);
              r := R.RawExpr("((" + n + ".0 / " + d + ".0" + ") as " + genType.ToString(IND) + ")");
            }
          }

          isOwned := true;
          readIdents := {};
        }
        case Literal(StringLiteral(l)) => {
          // TODO(shadaj): handle unicode properly
          r := R.RawExpr("\"" + l + "\".chars().collect::<Vec<char>>()");
          isOwned := true;
          readIdents := {};
        }
        case Literal(CharLiteral(c)) => {
          r := R.RawExpr("::std::primitive::char::from_u32(" + Strings.OfNat(c as nat) + ").unwrap()");
          isOwned := true;
          readIdents := {};
        }
        case Literal(Null(tpe)) => {
          // TODO: Mikael. Null will be std::ptr::null, not Option::None.
          var tpeGen := GenType(tpe, false, false);
          r := R.RawExpr("(None as " + tpeGen.ToString(IND) + ")");
          isOwned := true;
          readIdents := {};
        }
        case Ident(name) => {
          var s := escapeIdent(name);
          if !(name in params) { // TODO(mikael) have a table to know which names are borrowed
            r := R.RawExpr("(&" + s + ")");
          }

          if mustOwn {
            s := s + ".clone()";
            isOwned := true;
          } else {
            isOwned := false;
          }
          r := R.RawExpr(s);

          readIdents := {name};
        }
        case Companion(path) => {
          var p := GenPath(path);
          r := R.RawExpr(p);
          isOwned := true;
          readIdents := {};
        }
        case InitializationValue(typ) => {
          // TODO (Mikael): Make InitializationValue disappear.
          var typExpr := GenType(typ, false, false);
          r := R.RawExpr("<" + typExpr.ToString(IND) + " as std::default::Default>::default()");
          isOwned := true;
          readIdents := {};
        }
        case Tuple(values) => {
          var s := "(";
          readIdents := {};

          var i := 0;
          while i < |values| {
            if i > 0 {
              s := s + " ";
            }

            var recursiveGen, _, recIdents := GenExpr(values[i], selfIdent, params, true);

            s := s + recursiveGen.ToString(IND) + ",";
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + ")";
          r := R.RawExpr(s);

          isOwned := true;
        }
        case New(path, typeArgs, args) => {
          var path := GenPath(path);
          // TODO(Mikael) Use allocate(...) here.
          var s := "::std::rc::Rc::new(" + path;
          if |typeArgs| > 0 {
            var i := 0;
            var typeExprs := [];
            while i < |typeArgs| {
              var typeExpr := GenType(typeArgs[i], false, false);
              typeExprs := typeExprs + [typeExpr];

              i := i + 1;
            }
            s := s + R.TypeApp("::", typeExprs).ToString(IND);
          }
          s := s + "::new(";
          readIdents := {};
          var i := 0;
          while i < |args| {
            if i > 0 {
              s := s + ", ";
            }

            var recursiveGen, _, recIdents := GenExpr(args[i], selfIdent, params, true);
            s := s + recursiveGen.ToString(IND);
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + "))";
          r := R.RawExpr(s);
          isOwned := true;
        }
        case NewArray(dims, typ) => {
          var i := |dims| - 1;
          var genTyp := GenType(typ, false, false);
          // TODO (Mikael): Prevent arrays from being initialized without initialization code
          var s := "<" + genTyp.ToString(IND) + " as ::std::default::Default>::default()";
          readIdents := {};
          while i >= 0 {
            var recursiveGen, _, recIdents := GenExpr(dims[i], selfIdent, params, true);

            s := "::std::rc::Rc::new(::std::cell::RefCell::new(vec![" + s + "; <usize as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()]))";
            readIdents := readIdents + recIdents;

            i := i - 1;
          }

          r := R.RawExpr(s);
          isOwned := true;
        }
        case DatatypeValue(path, typeArgs, variant, isCo, values) => {
          var path := GenPath(path);
          var s := "::std::rc::Rc::new(" + path + "::";
          if |typeArgs| > 0 {
            s := s + "<";
            var i := 0;
            while i < |typeArgs| {
              if i > 0 {
                s := s + ", ";
              }

              var typeExpr := GenType(typeArgs[i], false, false);
              s := s + typeExpr.ToString(IND);

              i := i + 1;
            }
            s := s + ">::";
          }
          s := s + escapeIdent(variant);
          readIdents := {};

          var i := 0;
          s := s + " {";
          while i < |values| {
            var (name, value) := values[i];
            if i > 0 {
              s := s + ", ";
            }

            if isCo {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, [], true);

              readIdents := readIdents + recIdents;
              var allReadCloned := "";
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned + "let " + escapeIdent(next) + " = " + escapeIdent(next) + ".clone();\n";
                recIdents := recIdents - {next};
              }
              s := s + escapeIdent(name) + ": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n" + allReadCloned + "move || (" + recursiveGen.ToString(IND) + ")})))";
            } else {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, params, true);

              s := s + escapeIdent(name) + ": " + "(" + recursiveGen.ToString(IND) + ")";
              readIdents := readIdents + recIdents;
            }
            i := i + 1;
          }
          s := s + " })";

          r := R.RawExpr(s);
          isOwned := true;
        }
        case Convert(expr, fromTpe, toTpe) => {
          assert {:split_here} true;
          if fromTpe == toTpe {
            var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
            r := recursiveGen;
            isOwned := recOwned;
            readIdents := recIdents;
          } else {
            match (fromTpe, toTpe) {
              case (Nullable(_), _) => {
                var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                var s := recursiveGen.ToString(IND);
                if !recOwned {
                  s := s + ".as_ref()";
                }

                s := s + ".unwrap()";
                r := R.RawExpr(s);
                isOwned := recOwned;
                readIdents := recIdents;
              }
              case (_, Nullable(_)) => {
                var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                var s := recursiveGen.ToString(IND);
                if !recOwned {
                  s := s + ".clone()";
                }

                s := "Some(" + s + ")";
                r := R.RawExpr(s);
                isOwned := true;
                readIdents := recIdents;
              }
              case (_, Path(_, _, Newtype(b, range, erase))) => {
                if fromTpe == b {
                  var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, mustOwn);

                  var potentialRhsType := NewtypeToRustType(b, range);
                  match potentialRhsType {
                    case Some(v) =>
                      r := R.ConversionNum(v, recursiveGen);
                      isOwned := true;
                    case None =>
                      if erase {
                        r := recursiveGen;
                      } else {
                        var rhsType := GenType(toTpe, true, false);
                        r := R.RawExpr(rhsType.ToString(IND) + "(" + recursiveGen.ToString(IND) + ")");
                      }
                      isOwned := recOwned;
                  }
                  readIdents := recIdents;
                } else {
                  assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
                  r, isOwned, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, params, mustOwn);
                }
              }
              case (Path(_, _, Newtype(b, range, erase)), _) => {
                if b == toTpe {
                  var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                  if erase {
                    r := recursiveGen;
                  } else {
                    r := R.RawExpr(recursiveGen.ToString(IND) + ".0");
                  }
                  isOwned := recOwned;
                  readIdents := recIdents;
                } else {
                  assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
                  r, isOwned, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, params, mustOwn);
                }
              }
              case (Primitive(Int), Primitive(Real)) => {
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
                r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::from_integer(" + recursiveGen.ToString(IND) + ")"));
                isOwned := true;
                readIdents := recIdents;
              }
              case (Primitive(Real), Primitive(Int)) => {
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, false);
                r := R.RawExpr("::dafny_runtime::dafny_rational_to_int(" + recursiveGen.ToString(IND) + ")");
                isOwned := true;
                readIdents := recIdents;
              }
              case (Primitive(Int), Passthrough(_)) => {
                var rhsType := GenType(toTpe, true, false);
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
                r := R.RawExpr("<" + rhsType.ToString(IND) + " as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()");
                isOwned := true;
                readIdents := recIdents;
              }
              case (Passthrough(_), Primitive(Int)) => {
                var rhsType := GenType(fromTpe, true, false);
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
                r := R.RcNew(R.RawExpr("::dafny_runtime::BigInt::from(" + recursiveGen.ToString(IND) + ")"));
                isOwned := true;
                readIdents := recIdents;
              }
              case (Primitive(Int), Primitive(Char)) => {
                var rhsType := GenType(toTpe, true, false);
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
                r := R.RawExpr("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()).unwrap()");
                isOwned := true;
                readIdents := recIdents;
              }
              case (Primitive(Char), Primitive(Int)) => {
                var rhsType := GenType(fromTpe, true, false);
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
                r := R.RcNew(R.RawExpr("::dafny_runtime::BigInt::from(" + recursiveGen.ToString(IND) + " as u32)"));
                isOwned := true;
                readIdents := recIdents;
              }
              case (Passthrough(_), Passthrough(_)) => {
                var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
                var toTpeGen := GenType(toTpe, true, false);

                r := R.RawExpr("((" + recursiveGen.ToString(IND) + ") as " + toTpeGen.ToString(IND) + ")");

                isOwned := true;
                readIdents := recIdents;
              }
              case _ => {
                var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                r := R.RawExpr("(" + recursiveGen.ToString(IND) + "/* conversion not yet implemented */)");
                isOwned := recOwned;
                readIdents := recIdents;
              }
            }
          }
        }
        case SeqConstruct(length, expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
          var lengthGen, _, lengthIdents := GenExpr(length, selfIdent, params, true);

          r := R.RawExpr("{\nlet _initializer = " + recursiveGen.ToString(IND) + ";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), " + lengthGen.ToString(IND) + ").map(|i| _initializer.0(&i)).collect::<Vec<_>>()\n}");

          readIdents := recIdents + lengthIdents;
          isOwned := true;
        }
        case SeqValue(exprs, typ) => {
          readIdents := {};

          var genTpe := GenType(typ, false, false);

          var i := 0;
          var s := "(vec![";
          i := 0;
          while i < |exprs| {
            if i > 0 {
              s := s + ", ";
            }

            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, params, true);
            readIdents := readIdents + recIdents;

            s := s + recursiveGen.ToString(IND);
            i := i + 1;
          }
          s := s + "] as Vec<" + genTpe.ToString(IND) + ">)";
          r := R.RawExpr(s);

          isOwned := true;
        }
        case SetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, params, true);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }

          var s := "vec![";
          i := 0;
          while i < |generatedValues| {
            if i > 0 {
              s := s + ", ";
            }

            var gen := generatedValues[i];
            s := s + gen.ToString(IND);
            i := i + 1;
          }
          s := s + "].into_iter().collect::<std::collections::HashSet<_>>()";
          r := R.RawExpr(s);

          isOwned := true;
        }
        case MapValue(mapElems) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |mapElems| {
            var recursiveGenKey, _, recIdentsKey := GenExpr(mapElems[i].0, selfIdent, params, true);
            var recursiveGenValue, _, recIdentsValue := GenExpr(mapElems[i].1, selfIdent, params, true);

            generatedValues := generatedValues + [(recursiveGenKey, recursiveGenValue)];
            readIdents := readIdents + recIdentsKey + recIdentsValue;
            i := i + 1;
          }

          i := 0;
          var arguments := [];
          while i < |generatedValues| {
            var genKey := generatedValues[i].0;
            var genValue := generatedValues[i].1;

            arguments := arguments + [R.Tuple([genKey, genValue])];
            i := i + 1;
          }
          r := R.Call(R.RawExpr("::dafny_runtime::Map::from_array_owned"), [], [
            R.NewVec(arguments)
          ]);

          isOwned := true;
        }
        case This() => {
          match selfIdent {
            case Some(id) => {
              if mustOwn {
                r := R.RawExpr(id + ".clone()");
                isOwned := true;
              } else {
                if id == "self" {
                  r := R.RawExpr("self");
                } else {
                  r := R.RawExpr("&" + id);
                }
                isOwned := false;
              }

              readIdents := {id};
            }
            case None => {
              r := R.RawExpr("panic!(\"this outside of a method\")");
              isOwned := true;
              readIdents := {};
            }
          }
        }
        case Ite(cond, t, f) => {
          assert {:split_here} true;
          var cond, _, recIdentsCond := GenExpr(cond, selfIdent, params, true);
          var condString := cond.ToString(IND);

          var _, tHasToBeOwned, _ := GenExpr(t, selfIdent, params, mustOwn); // check if t has to be owned even if not requested
          var fExpr, fOwned, recIdentsF := GenExpr(f, selfIdent, params, tHasToBeOwned);
          var fString := fExpr.ToString(IND);
          var tExpr, _, recIdentsT := GenExpr(t, selfIdent, params, fOwned); // there's a chance that f forced ownership
          var tString := tExpr.ToString(IND);

          r := R.RawExpr("(if " + condString + " {\n" + tString + "\n} else {\n" + fString + "\n})");
          isOwned := fOwned;
          readIdents := recIdentsCond + recIdentsT + recIdentsF;
        }
        case UnOp(Not, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, params, true);

          r := R.RawExpr("!(" + recursiveGen.ToString(IND) + ")");
          isOwned := true;
          readIdents := recIdents;
        }
        case UnOp(BitwiseNot, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, params, true);

          r := R.RawExpr("~(" + recursiveGen.ToString(IND) + ")");
          isOwned := true;
          readIdents := recIdents;
        }
        case UnOp(Cardinality, e, format) => {
          var recursiveGen, recOwned, recIdents := GenExpr(e, selfIdent, params, false);

          r := R.RcNew(R.RawExpr("::dafny_runtime::BigInt::from((" + recursiveGen.ToString(IND) + ").len())"));
          isOwned := true;
          readIdents := recIdents;
        }
        case BinOp(op, lExpr, rExpr, format) => {
          var left, _, recIdentsL := GenExpr(lExpr, selfIdent, params, true);
          var right, _, recIdentsR := GenExpr(rExpr, selfIdent, params, true);

          match op {
            case In() => {
              r := R.Call(R.Select(right, "contains"), [], [R.Borrow(left)]);
            }
            case SetDifference() => {
              r := R.Call(R.Select(left, "difference"), [], [R.Borrow(right)]);
            }
            case MapMerge() => {
              r := R.Call(R.Select(left, "add_multiple"), [], [R.Borrow(right)]);
            }
            case MapSubtraction() => {
              r := R.Call(R.Select(left, "substract"), [], [R.Borrow(right)]);
            }
            case Concat() => {
              r := R.RawExpr("[" + left.ToString(IND) + ", " + right.ToString(IND) + "].concat()");
            }
            case _ => {

              if op in OpTable {
                r := R.Expr.BinaryOp(OpTable[op],
                                     left,
                                     right,
                                     format);
              } else {
                match op {
                  case Eq(referential, nullable) => {
                    if (referential) {
                      // TODO: Render using a call with two expressions
                      if (nullable) {
                        r := R.Call(R.RawExpr("::dafny_runtime::nullable_referential_equality"), [], [left, right]);
                      } else {
                        r := R.Call(R.RawExpr("::std::rc::Rc::ptr_eq"), [], [R.Borrow(left), R.Borrow(right)]);
                      }
                    } else {
                      r := R.BinaryOp("==", left, right, DAST.Format.BinOpFormat.NoFormat());
                    }
                  }
                  case EuclidianDiv() => {
                    r := R.Call(R.RawExpr("::dafny_runtime::euclidian_division"), [], [left, right]);
                  }
                  case EuclidianMod() => {
                    r := R.Call(R.RawExpr("::dafny_runtime::euclidian_modulo"), [], [left, right]);
                  }
                  case LtChar() => {
                    r := R.Call(R.RawExpr("::dafny_runtime::char_lt"), [], [left, right]);
                  }
                  case Passthrough(op) => {
                    r := R.Expr.BinaryOp(op, left, right, format);
                  }
                }
              }
            }
          }

          isOwned := true;
          readIdents := recIdentsL + recIdentsR;
        }
        case ArrayLen(expr, dim) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);

          if dim == 0 {
            r := R.RawExpr("::dafny_runtime::BigInt::from((" + recursiveGen.ToString(IND) + ").borrow().len())");
          } else {
            var s := R.RawExpr("::dafny_runtime::BigInt::from(m.borrow().len())").ToString(IND);
            var i := 1;
            while i < dim {
              s := "m.borrow().get(0).map(|m| " + s + ").unwrap_or(::dafny_runtime::BigInt::from(0))";
              i := i + 1;
            }

            r := R.RcNew(R.RawExpr("(" + recursiveGen.ToString(IND) + ")" + ".borrow().get(0).map(|m| " + s + ").unwrap_or(::dafny_runtime::BigInt::from(0))"));
          }

          isOwned := true;
          readIdents := recIdents;
        }
        case MapKeys(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
          isOwned := true;
          readIdents := recIdents;
          r := R.Call(R.Select(recursiveGen, "keys"), [], []);
        }
        case MapValues(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, true);
          isOwned := true;
          readIdents := recIdents;
          r := R.Call(R.Select(recursiveGen, "values"), [], []);
        }
        case SelectFn(on, field, isDatatype, isStatic, arity) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, false);
          var s: string;
          var onString := onExpr.ToString(IND);

          if isStatic {
            s := onString + "::" + escapeIdent(field);
          } else {
            s := "{\n";
            s := s + "let callTarget = (" + onString + (if onOwned then ")" else ").clone()") + ";\n";
            var args := "";
            var i := 0;
            while i < arity {
              if i > 0 {
                args := args + ", ";
              }
              args := args + "arg" + Strings.OfNat(i);
              i := i + 1;
            }
            s := s + "move |" + args + "| {\n";
            s := s + "callTarget." + field + "(" + args + ")\n";
            s := s + "}\n";
            s := s + "}";
          }

          var typeShape := "dyn ::std::ops::Fn(";
          var i := 0;
          while i < arity {
            if i > 0 {
              typeShape := typeShape + ", ";
            }
            typeShape := typeShape + "&_";
            i := i + 1;
          }

          typeShape := typeShape + ") -> _";

          s := "::dafny_runtime::FunctionWrapper(::std::rc::Rc::new(" + s + ") as ::std::rc::Rc<" + typeShape + ">)";
          r := R.RawExpr(s);

          isOwned := true;
          readIdents := recIdents;
        }
        case Select(Companion(c), field, isConstant, isDatatype) => {
          var onExpr, onOwned, recIdents := GenExpr(Companion(c), selfIdent, params, false);

          r := R.RawExpr(onExpr.ToString(IND) + "::" + escapeIdent(field) + "()");

          isOwned := true;
          readIdents := recIdents;
        }
        case Select(on, field, isConstant, isDatatype) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, false);
          var s: string;
          if isDatatype || isConstant {
            s := "(" + onExpr.ToString(IND) + ")" + "." + escapeIdent(field) + "()";
            if isConstant {
              s := "&" + s;
            }

            if mustOwn {
              s := "(" + s + ").clone()";
              isOwned := true;
            } else {
              isOwned := false;
            }
          } else {
            s := "::std::ops::Deref::deref(&((" + onExpr.ToString(IND) + ")" + "." + escapeIdent(field) + ".borrow()))";
            s := "(" + s + ").clone()"; // TODO(shadaj): think through when we can avoid cloning
            isOwned := true;
          }
          r := R.RawExpr(s);
          readIdents := recIdents;
        }
        case Index(on, collKind, indices) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, false);
          readIdents := recIdents;

          var s := onExpr.ToString(IND);

          var i := 0;
          while i < |indices| {
            if collKind == CollKind.Array {
              s := "(" + s + ").borrow()";
            }

            if collKind == CollKind.Map {
              var idx, idxOwned, recIdentsIdx := GenExpr(indices[i], selfIdent, params, false);
              s := "(" + s + ")[" + (if idxOwned then "&" else "") + idx.ToString(IND) + "]";
              readIdents := readIdents + recIdentsIdx;
            } else {
              var idx, _, recIdentsIdx := GenExpr(indices[i], selfIdent, params, true);

              s := "(" + s + ")[<usize as ::dafny_runtime::NumCast>::from(" + idx.ToString(IND) + ").unwrap()]";
              readIdents := readIdents + recIdentsIdx;
            }

            i := i + 1;
          }

          if mustOwn {
            s := "(" + s + ").clone()";
            isOwned := true;
          } else {
            s := "(&" + s + ")";
            isOwned := false;
          }
          r := R.RawExpr(s);
        }
        case IndexRange(on, isArray, low, high) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, false);
          readIdents := recIdents;

          var s := onExpr.ToString(IND);

          var lowString := None;
          match low {
            case Some(l) => {
              var lString, _, recIdentsL := GenExpr(l, selfIdent, params, true);

              lowString := Some(lString);
              readIdents := readIdents + recIdentsL;
            }
            case None => {}
          }

          var highString := None;
          match high {
            case Some(h) => {
              var hString, _, recIdentsH := GenExpr(h, selfIdent, params, true);

              highString := Some(hString);
              readIdents := readIdents + recIdentsH;
            }
            case None => {}
          }

          if isArray {
            s := "(" + s + ").borrow()";
          }

          s := "(" + s + ")" + "[" +
          (
            match lowString {
              case Some(l) => "<usize as ::dafny_runtime::NumCast>::from(" + l.ToString(IND) + ").unwrap()"
              case None => ""
            })
          + ".." + (
            match highString {
              case Some(h) => "<usize as ::dafny_runtime::NumCast>::from(" + h.ToString(IND) + ").unwrap()"
              case None => ""
            }) + "]";

          s := "(" + s + ".to_vec())";
          r := R.RawExpr(s);
          isOwned := true;
        }
        case TupleSelect(on, idx) => {
          var onExpr, _, recIdents := GenExpr(on, selfIdent, params, false);
          var s := "(" + onExpr.ToString(IND) + ")." + Strings.OfNat(idx);
          if mustOwn {
            s := "(" + s + ")" + ".clone()";
            isOwned := true;
          } else {
            s := "&" + s;
            isOwned := false;
          }
          r := R.RawExpr(s);
          readIdents := recIdents;
        }
        case Call(on, name, typeArgs, args) => {
          readIdents := {};

          var typeExprs := [];
          if (|typeArgs| >= 1) {
            var typeI := 0;
            while typeI < |typeArgs| {

              var typeExpr := GenType(typeArgs[typeI], false, false);
              typeExprs := typeExprs + [typeExpr];

              typeI := typeI + 1;
            }
          }

          var argExprs := [];
          var i := 0;
          while i < |args| {
            var argExpr, isOwned, argIdents := GenExpr(args[i], selfIdent, params, false);
            if isOwned {
              argExpr := R.Borrow(argExpr);
            }

            argExprs := argExprs + [argExpr];
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var enclosingExpr, _, recIdents := GenExpr(on, selfIdent, params, false);
          readIdents := readIdents + recIdents;
          var enclosingString := enclosingExpr.ToString(IND);
          var renderedName := match name {
            case Name(ident) => escapeIdent(ident)
            case MapBuilderAdd | SetBuilderAdd => "add"
            case MapBuilderBuild | SetBuilderBuild => "build"
          };
          match on {
            case Companion(_) => {
              enclosingString := enclosingString + "::" + renderedName;
            }
            case _ => {
              enclosingString := "(" + enclosingString + ")." + renderedName;
            }
          }

          r := R.Call(R.RawExpr(enclosingString), typeExprs, argExprs);
          isOwned := true;
        }
        case Lambda(params, retType, body) => {
          var paramNames := [];
          var i := 0;
          while i < |params| {
            paramNames := paramNames + [params[i].name];
            i := i + 1;
          }

          var recursiveGen, recIdents := GenStmts(body, if selfIdent != None then Some("_this") else None, paramNames, true, R.RawExpr(""));
          readIdents := {};
          var allReadCloned := "";
          while recIdents != {} decreases recIdents {
            var next: string :| next in recIdents;

            if selfIdent != None && next == "_this" {
              if selfIdent != None {
                allReadCloned := allReadCloned + "let _this = self.clone();\n";
              }
            } else if !(next in paramNames) {
              allReadCloned := allReadCloned + "let " + escapeIdent(next) + " = " + escapeIdent(next) + ".clone();\n";
              readIdents := readIdents + {next};
            }

            recIdents := recIdents - {next};
          }

          var paramsString := "";
          var paramTypes := "";
          i := 0;
          while i < |params| {
            if i > 0 {
              paramsString := paramsString + ", ";
              paramTypes := paramTypes + ", ";
            }

            var typStr := GenType(params[i].typ, false, true);

            paramsString := paramsString + escapeIdent(params[i].name) + ": " + R.Borrowed(typStr).ToString(IND);
            paramTypes := paramTypes + R.Borrowed(typStr).ToString(IND);
            i := i + 1;
          }

          var retTypeGen := GenType(retType, false, true);

          r := R.RawExpr("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn(" + paramTypes + ") -> " + retTypeGen.ToString(IND) + ">>({\n" + allReadCloned + "::std::rc::Rc::new(move |" + paramsString + "| -> " + retTypeGen.ToString(IND) + " {\n" + recursiveGen.ToString(IND) + "\n})})");
          isOwned := true;
        }
        case BetaRedex(values, retType, expr) => {
          var paramNames := [];
          var paramNamesSet := {};
          var i := 0;
          while i < |values| {
            paramNames := paramNames + [values[i].0.name];
            paramNamesSet := paramNamesSet + {values[i].0.name};
            i := i + 1;
          }

          readIdents := {};
          var s := "{\n";

          var paramsString := "";
          i := 0;
          while i < |values| {
            if i > 0 {
              paramsString := paramsString + ", ";
            }

            var typStr := GenType(values[i].0.typ, false, true);

            var valueGen, _, recIdents := GenExpr(values[i].1, selfIdent, params, true);
            s := s + "let " + escapeIdent(values[i].0.name) + ": " + typStr.ToString(IND) + " = ";
            readIdents := readIdents + recIdents;

            s := s + valueGen.ToString(IND) + ";\n";
            i := i + 1;
          }

          var recGen, recOwned, recIdents := GenExpr(expr, selfIdent, paramNames, mustOwn);
          readIdents := recIdents - paramNamesSet;

          s := s  + recGen.ToString(IND) + "\n}";
          r := R.RawExpr(s);
          isOwned := recOwned;
        }
        case IIFE(name, tpe, value, iifeBody) => {
          var valueGen, _, recIdents := GenExpr(value, selfIdent, params, true);

          readIdents := recIdents;
          var valueTypeGen := GenType(tpe, false, true);
          var bodyGen, _, bodyIdents := GenExpr(iifeBody, selfIdent, params, true);
          readIdents := readIdents + (bodyIdents - {name.id});

          r := R.RawExpr("{\nlet " + escapeIdent(name.id) + ": " + valueTypeGen.ToString(IND) + " = " + valueGen.ToString(IND) + ";\n" + bodyGen.ToString(IND) + "\n}");
          isOwned := true;
        }
        case Apply(func, args) => {
          var funcExpr, _, recIdents := GenExpr(func, selfIdent, params, false);
          readIdents := recIdents;

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, isOwned, argIdents := GenExpr(args[i], selfIdent, params, false);
            var argExprString := argExpr.ToString(IND);
            if isOwned {
              argExprString := "&" + argExprString;
            }

            argString := argString + argExprString;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          r := R.RawExpr("((" + funcExpr.ToString(IND) + ").0" + "(" + argString + "))");
          isOwned := true;
        }
        case TypeTest(on, dType, variant) => {
          var exprGen, _, recIdents := GenExpr(on, selfIdent, params, false);
          var dTypePath := GenPath(dType);
          r := R.RawExpr("matches!(" + exprGen.ToString(IND) + ".as_ref(), " + dTypePath + "::" + escapeIdent(variant) + "{ .. })");
          isOwned := true;
          readIdents := recIdents;
        }
        case BoolBoundedPool() => {
          r := R.RawExpr("[false, true]");
          isOwned := true;
          readIdents := {};
        }
        case SetBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, params, false);
          r := R.RawExpr("(" + exprGen.ToString(IND) + ").iter()");
          isOwned := true;
          readIdents := recIdents;
        }
        case SeqBoundedPool(of, includeDuplicates) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, params, false);
          var s := "(" + exprGen.ToString(IND) + ").iter()";
          if !includeDuplicates {
            s := "::dafny_runtime::itertools::Itertools::unique(" + s + ")";
          }
          r := R.RawExpr(s);
          isOwned := true;
          readIdents := recIdents;
        }
        case IntRange(lo, hi) => {
          var lo, _, recIdentsLo := GenExpr(lo, selfIdent, params, true);
          var hi, _, recIdentsHi := GenExpr(hi, selfIdent, params, true);

          r := R.RawExpr("::dafny_runtime::integer_range(" + lo.ToString(IND) + ", " + hi.ToString(IND) + ")");
          isOwned := true;
          readIdents := recIdentsLo + recIdentsHi;
        }
        case MapBuilder(keyType, valueType) => {
          var kType := GenType(keyType, false, false);
          var vType := GenType(valueType, false, false);
          isOwned := true;
          readIdents := {};
          r := R.RawExpr("::dafny_runtime::MapBuilder::<" + kType.ToString(IND) + ", " + vType.ToString(IND) + ">::new()");
        }
        case SetBuilder(elemType) => {
          var eType := GenType(elemType, false, false);
          isOwned := true;
          readIdents := {};
          r := R.RawExpr("::dafny_runtime::SetBuilder::<" + eType.ToString(IND) + ">::new()");
        }
      }
    }

    static method Compile(p: seq<Module>) returns (s: string) {
      s := "#![allow(warnings, unconditional_panic)]\n";
      s := s + "#![allow(nonstandard_style)]\n";
      s := s + "extern crate dafny_runtime;\n";

      var i := 0;
      while i < |p| {
        var generated: string;
        var m := GenModule(p[i], []);
        generated := m.ToString("");

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "\nfn main() {\n";
      var i := 0;
      while i < |fullName| {
        if i > 0 {
          s := s + "::";
        }
        s := s + escapeIdent(fullName[i]);
        i := i + 1;
      }
      s := s + "();\n}";
    }
  }
}
