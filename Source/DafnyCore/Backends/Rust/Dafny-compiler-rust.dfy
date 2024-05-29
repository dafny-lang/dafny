include "../Dafny/AST.dfy"
  // Dafny to Rust compilation tenets:
  // - The Compiled Dafny AST should be minimal
  // - The generated code should look idiomatic and close to the original Dafny file if possible

// Rust AST
module RAST
  // All ToString methods should produce well-formed Rust code
{
  import opened Std.Wrappers
  import opened DAST.Format
  import Strings = Std.Strings

  const IND := "  "

  datatype Mod =
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
    NamelessFormal(visibility: Visibility, tpe: Type)
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
    TypeApp(std_type.MSel("rc").MSel("Rc"), [underlying])
  }
  function RefCell(underlying: Type): Type {
    TypeApp(std_type.MSel("cell").MSel("RefCell"), [underlying])
  }
  function Vec(underlying: Type): Type {
    TypeApp(std_type.MSel("vec").MSel("Vec"), [underlying])
  }
  function NewVec(elements: seq<Expr>): Expr {
    Call(Identifier("vec!"), [], elements)
  }
  function Clone(underlying: Expr): Expr {
    Call(Select(underlying, "clone"), [], [])
  }
  function Borrow(underlying: Expr): Expr {
    UnaryOp("&", underlying, UnaryOpFormat.NoFormat)
  }
  function BorrowMut(underlying: Expr): Expr {
    UnaryOp("&mut", underlying, UnaryOpFormat.NoFormat)
  }

  const CloneTrait := RawType("Clone")
  const DafnyPrintTrait := RawType("::dafny_runtime::DafnyPrint")
  const DefaultTrait := RawType("::std::default::Default")
  const StaticTrait := RawType("'static")

  function RawType(content: string): Type {
    TIdentifier(content)
  }

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
  {
    function ToString(ind: string): string {
      match this {
        case TIdentifier(underlying) => underlying
        case TMemberSelect(underlying, name) => underlying.ToString(ind) + "::" + name
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
          base.ToString(ind) +
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

    function MSel(name: string): Type {
      TMemberSelect(this, name)
    }

    function Apply1(arg: Type): Type {
      TypeApp(this, [arg])
    }
  }

  const global_type := TIdentifier("")
  const std_type := global_type.MSel("std")
  const cell_type := std_type.MSel("cell")
  const refcell_type := cell_type.MSel("RefCell")
  const dafny_runtime_type := global_type.MSel("dafny_runtime")

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
    | FnDecl(pub: Visibility, fun: Fn)
  {
    function ToString(ind: string): string {
      if FnDecl? then
        (if pub == PUB then "pub " else "") + fun.ToString(ind)
      else assert RawImplMember?; content
    }
  }
  datatype Visibility = PUB | PRIV

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
    ghost function Height(): nat {
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
    ghost function Height(): nat {
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

  datatype Associativity = LeftToRight | RightToLeft | RequiresParentheses
  datatype PrintingInfo =
    | UnknownPrecedence()
    | Precedence(precedence: nat)
    | SuffixPrecedence(precedence: nat)
    | PrecedenceAssociativity(precedence: nat, associativity: Associativity)
  {
    predicate NeedParenthesesFor(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then true
      else false
    }
    predicate NeedParenthesesForLeft(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then
        precedence < underlying.precedence || !PrecedenceAssociativity? || !associativity.LeftToRight?
      else false
    }
    predicate NeedParenthesesForRight(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then
        precedence < underlying.precedence || !PrecedenceAssociativity? || !associativity.RightToLeft?
      else false
    }
    lemma Tests()
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForLeft(PrecedenceAssociativity(20, LeftToRight)) == false
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForRight(PrecedenceAssociativity(20, LeftToRight)) == true
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForRight(PrecedenceAssociativity(20, RightToLeft)) == false
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForLeft(PrecedenceAssociativity(20, RightToLeft)) == true
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForLeft(PrecedenceAssociativity(30, LeftToRight)) == true
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForRight(PrecedenceAssociativity(30, RightToLeft)) == true
    {
    }
  }


  datatype Expr =
      RawExpr(content: string)
    | Identifier(name: string) // Can be empty for global in MemberSelect
    | Match(matchee: Expr, cases: seq<MatchCase>)
    | StmtExpr(stmt: Expr, rhs: Expr)
    | Block(underlying: Expr)
    | StructBuild(name: string, assignments: seq<AssignIdentifier>)
    | Tuple(arguments: seq<Expr>)
    | UnaryOp(op1: string, underlying: Expr, format: Format.UnaryOpFormat)
    | BinaryOp(op2: string, left: Expr, right: Expr, format2: Format.BinaryOpFormat)
    | TypeAscription(left: Expr, tpe: Type)
    | LiteralInt(value: string)
    | LiteralString(value: string, binary: bool)
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
    | MemberSelect(obj: Expr, name: string)
  {
    predicate NoExtraSemicolonAfter() {
      DeclareVar? || AssignVar? || Break? || Continue? || Return? ||
      (RawExpr? && |content| > 0 && content[|content| - 1] == ';')
    }
    // Taken from https://doc.rust-lang.org/reference/expressions.html
    const printingInfo: PrintingInfo :=
      match this {
        case RawExpr(_) => UnknownPrecedence()
        case Identifier(_) => Precedence(1)
        case LiteralInt(_) => Precedence(1)
        case LiteralString(_, _) => Precedence(1)
        // Paths => Precedence(1)
        // Method call => Precedence(2)
        // Field expression => PrecedenceAssociativity(3, LeftToRight)
        // case function call | ArrayIndexing => Precedence(4)
        case UnaryOp(op, underlying, format) =>
          match op {
            case "?" => SuffixPrecedence(5)
            case "-" | "*" | "!" | "&" | "&mut" => Precedence(6)
            case _ => UnknownPrecedence()
          }
        case Select(underlying, name) => PrecedenceAssociativity(2, LeftToRight)
        case MemberSelect(underlying, name) => PrecedenceAssociativity(2, LeftToRight)
        case Call(_, _, _) => PrecedenceAssociativity(2, LeftToRight)
        case TypeAscription(left, tpe) =>
          PrecedenceAssociativity(10, LeftToRight)
        case BinaryOp(op2, left, right, format) =>
          match op2 {
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
        case _ => UnknownPrecedence()
      }

    ghost function Height(): nat {
      match this {
        case Identifier(_) => 1
        case LiteralInt(_) => 1
        case LiteralString(_, _) => 1
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
        case TypeAscription(left, tpe) => 1 + left.Height()
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
        case Select(expression, name) =>
          1 + expression.Height()
        case MemberSelect(expression, name) =>
          1 + expression.Height()
        case _ =>
          assert RawExpr?;
          1
      }
    }

    // Wish: Prove that Optimize() preserves semantics, if any
    // TODO: Ensure that even without Optimize(), tests pass
    opaque function Optimize(): (r: Expr)
      ensures this == r || r.Height() < this.Height()
    {
      match this {
        case UnaryOp("&", Call(Select(underlying, "clone"), typeArgs, args), format) =>
          if typeArgs == [] && args == [] then
            assert Select(underlying, "clone").Height() == 1 + underlying.Height();
            assert Call(Select(underlying, "clone"), typeArgs, args).Height() == 2 + underlying.Height();
            assert UnaryOp("&", underlying, format).Height() == 1 + underlying.Height();
            UnaryOp("&", underlying, format)
          else
            this

        case UnaryOp("!", BinaryOp("==", left, right, format),
          CombineFormat()) =>
          assert BinaryOp("==", left, right, format).Height()
              == BinaryOp("!=", left, right, BinaryOpFormat.NoFormat()).Height();
          BinaryOp("!=", left, right, BinaryOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, NoFormat()),
          CombineFormat()) =>
          assert BinaryOp(">=", left, right, BinaryOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinaryOpFormat.NoFormat()).Height();
          BinaryOp(">=", left, right, BinaryOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, ReverseFormat()),
          CombineFormat()) =>
          assert BinaryOp("<=", right, left, BinaryOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinaryOpFormat.ReverseFormat()).Height();
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
        // Temporarily disabling these because the Dafny->C# code generator
        // creates an explicit branch for every other data constructor at every nested level,
        // so this function explodes into over 400 lines of C# and we get
        // "error CS8078: An expression is too long or complex to compile"
        // on newer Mac OS'.
        //
        // case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(AssignVar(name2, rhs), last)) =>
        //   if name == name2 then
        //     var rewriting := StmtExpr(DeclareVar(mod, name, Some(tpe), Some(rhs)), last);
        //     assert rewriting.Height() < this.Height() by {
        //       assert StmtExpr(AssignVar(name2, rhs), last).Height() ==
        //              1 + max(AssignVar(name2, rhs).Height(), last.Height()) ==
        //              1 + max(1 + rhs.Height(), last.Height());
        //       assert this.Height() == 2 + max(1, 1 + max(1 + rhs.Height(), last.Height()));
        //       assert rewriting.Height() == 1 + max(1 + rhs.Height(), last.Height());
        //     }
        //     rewriting
        //   else
        //     this
        case _ => this
      }
    }

    predicate LeftRequiresParentheses(left: Expr) {
      printingInfo.NeedParenthesesForLeft(left.printingInfo)
    }
    function LeftParentheses(left: Expr): (string, string) {
      if LeftRequiresParentheses(left) then
        ("(", ")")
      else
        ("", "")
    }

    predicate RightRequiresParentheses(right: Expr) {
      printingInfo.NeedParenthesesForRight(right.printingInfo)
    }


    function RightParentheses(right: Expr): (string, string) {
      if RightRequiresParentheses(right) then
        ("(", ")")
      else
        ("", "")
    }

    function RightMostIdentifier(): Option<string> {
      match this {
        case MemberSelect(_, id) => Some(id)
        case _ => None
      }
    }

    function ToString(ind: string): string
      decreases Height()
    {
      match this.Optimize() {
        case Identifier(name) => name
        case LiteralInt(number) => number
        case LiteralString(characters, binary) =>
          (if binary then "b" else "") +
          "\"" + characters + "\""
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
          if stmt.RawExpr? && stmt.content == "" then rhs.ToString(ind) else
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
            if printingInfo.NeedParenthesesFor(underlying.printingInfo) then
              ("(", ")")
            else
              ("", "");
          var leftOp := if op == "&mut" && leftP != "(" then op + " " else if op == "?" then "" else op;
          var rightOp := if op == "?" then op else "";

          leftOp + leftP  + underlying.ToString(ind) + rightP + rightOp
        case TypeAscription(left, tpe) =>
          var (leftLeftP, leftRightP) := LeftParentheses(left);
          leftLeftP + left.ToString(IND) + leftRightP + " as " + tpe.ToString(IND)
        case BinaryOp(op2, left, right, format) =>
          var (leftLeftP, leftRighP) := LeftParentheses(left);
          var (rightLeftP, rightRightP) := RightParentheses(right);
          var opRendered := " " + op2 + " ";
          var indLeft := if leftLeftP == "(" then ind + IND else ind;
          var indRight := if rightLeftP == "(" then ind + IND else ind;
          leftLeftP + left.ToString(indLeft) + leftRighP + opRendered + rightLeftP + right.ToString(indRight) + rightRightP
        case DeclareVar(declareType, name, optType, optExpr) =>
          "let " + (if declareType == MUT then "mut " else "") +
          name + (if optType.Some? then ": " + optType.value.ToString(ind + IND) else "") +

          (if optExpr.Some? then
             var optExprString := optExpr.value.ToString(ind + IND);
             if optExprString == "" then
               "= /*issue with empty RHS*/" +
               if optExpr.value.RawExpr? then "Empty Raw expr" else
               if optExpr.value.LiteralString? then "Empty string literal" else
               if optExpr.value.LiteralInt? then "Empty int literal" else
               "Another case"
             else " = " + optExprString else "") + ";"
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
          var (leftP, rightP) := LeftParentheses(expr);
          var (leftCallP, rightCallP) := match expr.RightMostIdentifier() {
            case Some("seq!") | Some("map!")  =>
              ("[","]")
            case Some("set!") | Some("multiset!") =>
              ("{","}")
            case _ =>
              ("(", ")")
          };
          leftP + expr.ToString(ind) + rightP + (
            if |tpes| == 0 then ""
            else
              "::<" + SeqToString(tpes, (tpe: Type) => tpe.ToString(ind + IND), ", ") +">"
          ) + leftCallP + SeqToString(args, (arg: Expr) requires arg.Height() < this.Height() => arg.ToString(ind + IND), ", ")+ rightCallP
        case Select(expression, name) =>
          var (leftP, rightP) := LeftParentheses(expression);
          leftP + expression.ToString(ind) + rightP + "." + name
        case MemberSelect(expression, name) =>
          var (leftP, rightP) := LeftParentheses(expression);
          leftP + expression.ToString(ind) + rightP + "::" + name
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

    // Helpers

    function Sel(name: string): Expr {
      Select(this, name)
    }
    function MSel(name: string): Expr {
      MemberSelect(this, name)
    }

    function Apply(typeParameters: seq<Type>, arguments: seq<Expr>): Expr {
      Call(this, typeParameters, arguments)
    }

    function Apply1(argument: Expr): Expr {
      Call(this, [], [argument])
    }
  }

  const global := Identifier("")

  const dafny_runtime := global.MSel("dafny_runtime")
  const dafny_runtime_Set := dafny_runtime.MSel("Set")
  const dafny_runtime_Set_from_array := dafny_runtime_Set.MSel("from_array")
  const dafny_runtime_Sequence := dafny_runtime.MSel("Sequence")
  const Sequence_from_array_owned := dafny_runtime_Sequence.MSel("from_array_owned")
  const Sequence_from_array := dafny_runtime_Sequence.MSel("from_array")
  const dafny_runtime_Multiset := dafny_runtime.MSel("Multiset")
  const dafny_runtime_Multiset_from_array := dafny_runtime_Multiset.MSel("from_array")

  const std := global.MSel("std")

  const std_rc := std.MSel("rc")

  const std_rc_Rc := std_rc.MSel("Rc")

  const std_rc_Rc_new := std_rc_Rc.MSel("new")

  function RcNew(underlying: Expr): Expr {
    Call(std_rc_Rc_new, [], [underlying])
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

module {:extern "DCOMP"} DafnyToRustCompiler {
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

  predicate is_tuple_builder(i: string)
    // A tuple builder identifier looks like ___hMake0 to ___hMake99
  {
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

  predicate is_idiomatic_rust_id(i: string) {
    0 < |i| && !has_special(i) && i !in reserved_rust
  }

  function escapeIdent(i: string): string {
    if is_tuple_numeric(i) then
      i
    else if is_tuple_builder(i) then
      better_tuple_builder_name(i)
    else if i in reserved_rust then
      "r#" + i
    else if is_idiomatic_rust_id(i) then
      idiomatic_rust(i)
    else if is_dafny_generated_id(i) then
      i // Dafny-generated identifiers like "_module", cannot be written in Dafny itself
    else
      var r := replaceDots(i);
      "r#_" + r
  }

  datatype Ownership = OwnershipOwned | OwnershipBorrowed | OwnershipBorrowedMut | OwnershipAutoBorrowed


  class COMP {
    const DafnyChar := if UnicodeChars then "DafnyChar" else "DafnyCharUTF16"
    const UnicodeChars: bool

    constructor(UnicodeChars: bool) {
      this.UnicodeChars := UnicodeChars;
    }
    method GenModule(mod: Module, containingPath: seq<Ident>) returns (s: R.Mod) {
      var body := GenModuleBody(mod.body, containingPath + [Ident.Ident(mod.name)]);

      s := if mod.isExtern then
        R.ExternMod(escapeIdent(mod.name))
      else
        R.Mod(escapeIdent(mod.name), body);
    }

    method GenModuleBody(body: seq<ModuleItem>, containingPath: seq<Ident>) returns (s: seq<R.ModDecl>) {
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

    method GenTypeParameters(params: seq<Type>)
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

    method GenClass(c: Class, path: seq<Ident>) returns (s: seq<R.ModDecl>) {
      var typeParamsSet, sTypeParams, sConstrainedTypeParams, whereConstraints := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParam.ToStringMultiple(sConstrainedTypeParams, R.IND + R.IND);

      var fields: seq<R.Formal> := [];
      var fieldInits: seq<R.AssignIdentifier> := [];
      var fieldI := 0;
      while fieldI < |c.fields| {
        var field := c.fields[fieldI];
        var fieldType := GenType(field.formal.typ, false, false);
        fields := fields + [R.Formal("pub " + escapeIdent(field.formal.name), R.TypeApp(R.refcell_type, [fieldType]))];

        match field.defaultValue {
          case Some(e) => {
            var eStr, _, _ := GenExpr(e, None, [], OwnershipOwned);
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
        fields := fields + [R.Formal("_phantom_type_param_" + Strings.OfNat(typeParamI), R.TypeApp(R.std_type.MSel("marker").MSel("PhantomData"), [tpeGen]))];
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
        R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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
                  R.TypeApp(R.TIdentifier(pathStr), typeArgs),
                  R.Rc(R.TypeApp(R.TIdentifier(genSelfPath), typeParamsAsTypes)),
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
        R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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
          R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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
        R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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

    method GenTrait(t: Trait, containingPath: seq<Ident>) returns (s: string) {
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
                      [], R.TypeApp(R.TIdentifier(escapeIdent(t.name)), typeParams),
                      "",
                      implBody
                    )).ToString(IND);
    }

    method GenNewtype(c: Newtype) returns (s: seq<R.ModDecl>) {
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
          var eStr, _, _ := GenExpr(e, None, [], OwnershipOwned);
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
            R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
            whereConstraints,
            [body]))];
      s := s + [
        R.ImplDecl(R.ImplFor(
                     sConstrainedTypeParams,
                     R.DafnyPrintTrait,
                     R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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
            R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
            "",
            [R.RawImplMember("type Target = " + underlyingType.ToString(IND) + ";"),
             R.FnDecl(
               R.PRIV,
               R.Fn("deref", [],
                    [R.Formal.self], Some(R.RawType("&Self::Target")),
                    "",
                    Some(R.RawExpr("&self.0"))))]))];
    }

    method GenDatatype(c: Datatype) returns (s: seq<R.ModDecl>) {
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
                       R.TypeApp(R.dafny_runtime_type.MSel("LazyFieldWrapper"), [formalType]))];
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
          types := types + [R.TypeApp(R.TIdentifier("::std::marker::PhantomData::"), [genTp])];
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
             R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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
            R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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
              R.TypeApp(R.TIdentifier(escapeIdent(c.name)), typeParamsAsTypes),
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

    method GenTypeArgs(args: seq<Type>, inBinding: bool, inFn: bool) returns (s: seq<R.Type>) {
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

    method GenType(c: Type, inBinding: bool, inFn: bool) returns (s: R.Type) {
      match c {
        case Path(p, args, resolved) => {
          var t := GenPath(p);
          s := R.TIdentifier(t);

          var typeArgs := GenTypeArgs(args, inBinding, inFn);
          s := R.TypeApp(s, typeArgs);

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
          s := R.TypeApp(R.TIdentifier("::std::option::Option"), [innerExpr]);
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
          s := R.TypeApp(R.dafny_runtime_type.MSel("Sequence"), [elem]);
        }
        case Set(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Set"), [elem]);
        }
        case Multiset(element) => {
          var elem := GenType(element, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Multiset"), [elem]);
        }
        case Map(key, value) => {
          var keyType := GenType(key, inBinding, inFn);
          var valueType := GenType(value, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("Map"), [keyType, valueType]);
        }
        case MapBuilder(key, value) => {
          var keyType := GenType(key, inBinding, inFn);
          var valueType := GenType(value, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("MapBuilder"), [keyType, valueType]);
        }
        case SetBuilder(elem) => {
          var elemType := GenType(elem, inBinding, inFn);
          s := R.TypeApp(R.dafny_runtime_type.MSel("SetBuilder"), [elemType]);
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
            R.dafny_runtime_type.MSel("FunctionWrapper"),
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
            case Int => s := R.dafny_runtime_type.MSel("DafnyInt");
            case Real => s := R.dafny_runtime_type.MSel("BigRational");
            case String => s := R.TypeApp(R.dafny_runtime_type.MSel("Sequence"),
                                          [R.dafny_runtime_type.MSel(DafnyChar)]);
            case Bool => s := R.RawType("bool");
            case Char => s := R.dafny_runtime_type.MSel(DafnyChar);
          }
        }
        case Passthrough(v) => s := R.RawType(v);
      }
    }

    method GenClassImplBody(body: seq<ClassItem>, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>)
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

    method GenParams(params: seq<Formal>) returns (s: seq<R.Formal>) {
      s := [];
      var i := 0;
      while i < |params| {
        var param := params[i];
        var paramType := GenType(param.typ, false, false);
        s := s + [R.Formal(escapeIdent(param.name), R.Borrowed(paramType))];
        i := i + 1;
      }
    }

    method GenMethod(m: Method, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>) returns (s: R.ImplMember) {
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
              tupleArgs := tupleArgs + [R.Identifier(escapeIdent(outVar.id))];

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

    method GenStmts(stmts: seq<Statement>, selfIdent: Option<string>, params: seq<string>, isLast: bool, earlyReturn: R.Expr) returns (generated: R.Expr, readIdents: set<string>)
      decreases stmts, 1
    {
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

    method GenAssignLhs(lhs: AssignLhs, rhs: string, selfIdent: Option<string>, params: seq<string>) returns (generated: string, needsIIFE: bool, readIdents: set<string>)
      decreases lhs, 1
    {
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
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, OwnershipBorrowed);
          generated := "*(" + onExpr.ToString(IND) + "." + field + ".borrow_mut()) = " + rhs + ";";
          readIdents := recIdents;
          needsIIFE := true;
        }

        case Index(on, indices) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, OwnershipBorrowed);
          readIdents := recIdents;

          generated := "{\n";

          var i := 0;
          while i < |indices| {
            var idx, _, recIdentsIdx := GenExpr(indices[i], selfIdent, params, OwnershipOwned);

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

    method GenStmt(stmt: Statement, selfIdent: Option<string>, params: seq<string>, isLast: bool, earlyReturn: R.Expr) returns (generated: R.Expr, readIdents: set<string>)
      decreases stmt, 1
    {
      match stmt {
        case DeclareVar(name, typ, Some(expression)) => {
          var typeString := GenType(typ, true, false);
          var expr, _, recIdents := GenExpr(expression, selfIdent, params, OwnershipOwned);

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
          var exprGen, _, exprIdents := GenExpr(expression, selfIdent, params, OwnershipOwned);

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
          var cond, _, recIdents := GenExpr(cond, selfIdent, params, OwnershipOwned);
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
          var cond, _, recIdents := GenExpr(cond, selfIdent, params, OwnershipOwned);

          readIdents := recIdents;
          var body, bodyIdents := GenStmts(body, selfIdent, params, false, earlyReturn);
          readIdents := readIdents + bodyIdents;

          generated := R.Loop(Some(cond), body);
        }
        case Foreach(boundName, boundType, over, body) => {
          var over, _, recIdents := GenExpr(over, selfIdent, params, OwnershipOwned);

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
            generated := generated.Then(R.DeclareVar(R.MUT, escapeIdent(param), None, Some(R.Clone(R.Identifier(escapeIdent(param))))));
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
            typeArgString := R.TypeApp(R.TIdentifier("::"), typeArgsR).ToString(IND);
          }

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, ownership, argIdents := GenExpr(args[i], selfIdent, params, OwnershipBorrowed);
            var argExprString := argExpr.ToString(IND);

            argString := argString + argExprString;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var onExpr, _, enclosingIdents := GenExpr(on, selfIdent, params, OwnershipAutoBorrowed);
          readIdents := readIdents + enclosingIdents;
          var enclosingString := onExpr.ToString(IND);
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
          var expr, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
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
          var printedExpr, recOwnership, recIdents := GenExpr(e, selfIdent, params, OwnershipBorrowed);
          var printedExprString := printedExpr.ToString(IND);
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
        LtChar() := "<",
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

    static method FromOwned(r: R.Expr, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      ensures resultingOwnership != OwnershipAutoBorrowed
      ensures expectedOwnership != OwnershipAutoBorrowed
              ==> resultingOwnership == expectedOwnership
    {
      if expectedOwnership == OwnershipOwned || expectedOwnership == OwnershipAutoBorrowed {
        out := r;
        resultingOwnership := OwnershipOwned;
      } else if expectedOwnership == OwnershipBorrowed {
        out := R.Borrow(r);
        resultingOwnership := OwnershipBorrowed;
      } else {
        assert expectedOwnership == OwnershipBorrowedMut;
        out := R.BorrowMut(r);
        resultingOwnership := OwnershipBorrowedMut;
      }
    }

    static method FromOwnership(r: R.Expr, ownership: Ownership, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      requires ownership != OwnershipAutoBorrowed
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
    {
      if ownership == OwnershipOwned {
        out, resultingOwnership := FromOwned(r, expectedOwnership);
        return;
      } else if ownership == OwnershipBorrowed || ownership == OwnershipBorrowedMut {
        if expectedOwnership == OwnershipOwned {
          resultingOwnership := OwnershipOwned;
          out := R.Clone(r);
        } else if expectedOwnership == ownership
                  || expectedOwnership == OwnershipAutoBorrowed {
          resultingOwnership := ownership;
          out := r;
        } else if expectedOwnership == OwnershipBorrowed
                  && ownership == OwnershipBorrowedMut {
          resultingOwnership := OwnershipBorrowed;
          out := r;
        } else {
          assert expectedOwnership == OwnershipBorrowedMut;
          resultingOwnership := OwnershipBorrowedMut;
          out := R.BorrowMut(r); // Not sure if it will ever happen
        }
      } else {
        assert false;
      }
    }

    static predicate OwnershipGuarantee(expectedOwnership: Ownership, resultingOwnership: Ownership) {
      && (expectedOwnership != OwnershipAutoBorrowed ==>
            resultingOwnership == expectedOwnership)
      && resultingOwnership != OwnershipAutoBorrowed // We know what's going on
    }

    method GenExprLiteral(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Literal?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      match e {
        case Literal(BoolLiteral(false)) => {
          r, resultingOwnership :=
            FromOwned(R.RawExpr("false"), expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(BoolLiteral(true)) => {
          r, resultingOwnership :=
            FromOwned(R.RawExpr("true"), expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(IntLiteral(i, t)) => {
          match t {
            case Primitive(Int) => {
              if |i| <= 4 {
                r := R.dafny_runtime.MSel("DafnyInt").MSel("from").Apply1(R.LiteralInt(i));
              } else {
                r := R.dafny_runtime.MSel("DafnyInt").MSel("from").Apply1(
                  R.LiteralString(i, binary := true));
              }
            }
            case o => {
              var genType := GenType(o, false, false);
              r := R.TypeAscription(R.RawExpr(i), genType);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(DecLiteral(n, d, t)) => {
          match t {
            case Primitive(Real) => {
              r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\"" + n + "\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"" + d + "\", 10).unwrap())"));
            }
            case o => {
              var genType := GenType(o, false, false);
              r := R.TypeAscription(R.RawExpr("(" + n + ".0 / " + d + ".0" + ")"), genType);
            }
          }

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(StringLiteral(l)) => {
          r := R.dafny_runtime.MSel("string_of").Apply1(R.LiteralString(l, false));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(CharLiteral(c)) => {
          r := R.LiteralInt(Strings.OfNat(c as nat));
          if !UnicodeChars {
            r :=
              R.global.MSel("std").MSel("primitive")
              .MSel("char").MSel("from_u16")
              .Apply1(r).Sel("unwrap").Apply([], []);
          } else {
            r :=
              R.global.MSel("std").MSel("primitive")
              .MSel("char").MSel("from_u32")
              .Apply1(r).Sel("unwrap").Apply([], []);
          }
          r := R.dafny_runtime.MSel(DafnyChar).Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(Null(tpe)) => {
          // TODO: Mikael. Null will be std::ptr::null, not Option::None.
          var tpeGen := GenType(tpe, false, false);
          r := R.TypeAscription(R.RawExpr("None"), tpeGen);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
      }
    }

    method GenExprBinary(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.BinOp?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      var BinOp(op, lExpr, rExpr, format) := e;
      var becomesLeftCallsRight := match op {
        case SetMerge()
          | SetSubtraction()
          | SetIntersection()
          | SetDisjoint()
          | MapMerge()
          | MapSubtraction()
          | MultisetMerge()
          | MultisetSubtraction()
          | MultisetIntersection()
          | MultisetDisjoint()
          | Concat()
          => true
        case _ => false
      };
      var becomesRightCallsLeft := match op {
        case In() => true
        case _ => false
      };
      var becomesCallLeftRight := match op {
        case Eq(true, false) => true
        case _ => false
      };
      var expectedLeftOwnership :=
        if becomesLeftCallsRight then OwnershipAutoBorrowed
        else if becomesRightCallsLeft || becomesCallLeftRight then OwnershipBorrowed
        else OwnershipOwned;
      var expectedRightOwnership :=
        if becomesLeftCallsRight || becomesCallLeftRight then OwnershipBorrowed
        else if becomesRightCallsLeft then OwnershipAutoBorrowed
        else OwnershipOwned;
      var left, _, recIdentsL := GenExpr(lExpr, selfIdent, params, expectedLeftOwnership);
      var right, _, recIdentsR := GenExpr(rExpr, selfIdent, params, expectedRightOwnership);

      match op {
        case In() => {
          r := right.Sel("contains").Apply1(left);
        }
        case SeqProperPrefix() =>
          r := R.BinaryOp("<", left, right, format);
        case SeqPrefix() =>
          r := R.BinaryOp("<=", left, right, format);
        case SetMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case SetSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case SetIntersection() => {
          r := left.Sel("intersect").Apply1(right);
        }
        case Subset() => {
          r := R.BinaryOp("<=", left, right, format);
        }
        case ProperSubset() => {
          r := R.BinaryOp("<", left, right, format);
        }
        case SetDisjoint() => {
          r := left.Sel("disjoint").Apply1(right);
        }
        case MapMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case MapSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case MultisetMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case MultisetSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case MultisetIntersection() => {
          r := left.Sel("intersect").Apply1(right);
        }
        case Submultiset() => {
          r := R.BinaryOp("<=", left, right, format);
        }
        case ProperSubmultiset() => {
          r := R.BinaryOp("<", left, right, format);
        }
        case MultisetDisjoint() => {
          r := left.Sel("disjoint").Apply1(right);
        }
        case Concat() => {
          r := left.Sel("concat").Apply1(right);
        }
        case _ => {

          if op in OpTable {
            r := R.Expr.BinaryOp(
              OpTable[op],
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
                    r := R.Call(R.RawExpr("::std::rc::Rc::ptr_eq"), [], [left, right]);
                  }
                } else {
                  r := R.BinaryOp("==", left, right, DAST.Format.BinaryOpFormat.NoFormat());
                }
              }
              case EuclidianDiv() => {
                r := R.Call(R.RawExpr("::dafny_runtime::euclidian_division"), [], [left, right]);
              }
              case EuclidianMod() => {
                r := R.Call(R.RawExpr("::dafny_runtime::euclidian_modulo"), [], [left, right]);
              }
              case Passthrough(op) => {
                r := R.Expr.BinaryOp(op, left, right, format);
              }
            }
          }
        }
      }
      r, resultingOwnership := FromOwned(r, expectedOwnership);
      readIdents := recIdentsL + recIdentsR;
      return;
    }

    method GenExprConvertFromNullable(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      requires e.from != e.typ
      requires e.from.Nullable?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, expectedOwnership);
      r := recursiveGen;
      if recOwned == OwnershipOwned {
        r := r.Sel("as_ref").Apply([], []);
      }
      r := r.Sel("unwrap").Apply([], []);
      r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
      readIdents := recIdents;
    }

    method GenExprConvertToNullable(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      requires e.from != e.typ
      requires !e.from.Nullable? && e.typ.Nullable?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, expectedOwnership);
      r := recursiveGen;
      if recOwned == OwnershipOwned {
        r := r.Sel("clone").Apply([], []);
      }

      r := R.std.MSel("option").MSel("Option").MSel("Some").Apply([], [r]);
      r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
      readIdents := recIdents;
    }

    method GenExprConvertToNewtype(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      requires e.from != e.typ
      requires !e.from.Nullable? && e.typ.Path? && e.typ.resolved.Newtype?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var Path(_, _, Newtype(b, range, erase)) := toTpe;
      if fromTpe == b {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, expectedOwnership);

        var potentialRhsType := NewtypeToRustType(b, range);
        match potentialRhsType {
          case Some(v) =>
            r := R.ConversionNum(v, recursiveGen);
            r, resultingOwnership := FromOwned(r, expectedOwnership);
          case None =>
            if erase {
              r := recursiveGen;
            } else {
              var rhsType := GenType(toTpe, true, false);
              r := R.RawExpr(rhsType.ToString(IND) + "(" + recursiveGen.ToString(IND) + ")");
            }
            r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        }
        readIdents := recIdents;
        assert OwnershipGuarantee(expectedOwnership, resultingOwnership);
      } else {
        assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
        r, resultingOwnership, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, params, expectedOwnership);
        assert OwnershipGuarantee(expectedOwnership, resultingOwnership);
      }
    }


    method GenExprConvertFromNewtype(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      requires e.from != e.typ
      requires !e.from.Nullable? && (!e.typ.Path? || !e.typ.resolved.Newtype?)
      requires e.from.Path? && e.from.resolved.Newtype?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var Path(_, _, Newtype(b, range, erase)) := fromTpe;
      if b == toTpe {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, expectedOwnership);
        if erase {
          r := recursiveGen;
        } else {
          r := recursiveGen.Sel("0");
        }
        r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        readIdents := recIdents;
      } else {
        assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
        r, resultingOwnership, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, params, expectedOwnership);
      }
      assert OwnershipGuarantee(expectedOwnership, resultingOwnership);
    }

    method GenExprConvertNotImplemented(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, expectedOwnership);
      r := R.RawExpr("(" + recursiveGen.ToString(IND) + "/* conversion not yet implemented */)");
      r, resultingOwnership := FromOwned(r, expectedOwnership);
      readIdents := recIdents;
    }

    method GenExprConvert(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      if fromTpe == toTpe {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, params, expectedOwnership);
        r := recursiveGen;
        r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        readIdents := recIdents;
      } else {
        match (fromTpe, toTpe) {
          case (Nullable(_), _) => {
            r, resultingOwnership, readIdents := GenExprConvertFromNullable(e, selfIdent, params, expectedOwnership);
          }
          case (_, Nullable(_)) => {
            r, resultingOwnership, readIdents := GenExprConvertToNullable(e, selfIdent, params, expectedOwnership);
          }
          case (_, Path(_, _, Newtype(b, range, erase))) => {
            r, resultingOwnership, readIdents := GenExprConvertToNewtype(e, selfIdent, params, expectedOwnership);
          }
          case (Path(_, _, Newtype(b, range, erase)), _) => {
            r, resultingOwnership, readIdents := GenExprConvertFromNewtype(e, selfIdent, params, expectedOwnership);
          }
          case (Primitive(Int), Primitive(Real)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
            r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::from_integer(" + recursiveGen.ToString(IND) + ")"));
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Real), Primitive(Int)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipBorrowed);
            r := R.RawExpr("::dafny_runtime::dafny_rational_to_int(" + recursiveGen.ToString(IND) + ")");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Passthrough(_)) => {
            var rhsType := GenType(toTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
            r := R.RawExpr("<" + rhsType.ToString(IND) + " as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Primitive(Int)) => {
            var rhsType := GenType(fromTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
            r := R.RawExpr("::dafny_runtime::DafnyInt{data: ::dafny_runtime::BigInt::from(" + recursiveGen.ToString(IND) + ")}");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Primitive(Char)) => {
            var rhsType := GenType(toTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
            r := R.RawExpr("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()).unwrap()");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Char), Primitive(Int)) => {
            var rhsType := GenType(fromTpe, true, false);
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
            r := R.RawExpr("::dafny_runtime::DafnyInt{data: ::BigInt::from(" + recursiveGen.ToString(IND) + " as u32)}");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Passthrough(_)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
            var toTpeGen := GenType(toTpe, true, false);

            r := R.RawExpr("((" + recursiveGen.ToString(IND) + ") as " + toTpeGen.ToString(IND) + ")");

            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case _ => {
            r, resultingOwnership, readIdents := GenExprConvertNotImplemented(e, selfIdent, params, expectedOwnership);
          }
        }
      }
      assert OwnershipGuarantee(expectedOwnership, resultingOwnership);
      return;
    }
    method GenExpr(
      e: Expression,
      selfIdent: Option<string>,
      params: seq<string>,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 1 {
      match e {
        case Literal(_) =>
          r, resultingOwnership, readIdents :=
            GenExprLiteral(e, selfIdent, params, expectedOwnership);
        case Ident(name) => {
          r := R.Identifier(escapeIdent(name));
          var currentlyBorrowed := name in params; // Otherwise names are owned  // TODO(mikael) have a table to know which names are borrowed
          if expectedOwnership == OwnershipAutoBorrowed {
            resultingOwnership := OwnershipOwned;
            // No need to do anything
          } else if expectedOwnership == OwnershipBorrowedMut {
            r := R.BorrowMut(r); // Needs to be explicit for out-parameters on methods
            resultingOwnership := OwnershipBorrowedMut;
          } else if expectedOwnership == OwnershipOwned {
            r := R.Clone(r); // We don't transfer the ownership of an identifier
            resultingOwnership := OwnershipOwned;
          } else if currentlyBorrowed {
            assert expectedOwnership == OwnershipBorrowed;
            resultingOwnership := OwnershipBorrowed;
          } else {
            // It's currently owned.
            r := R.Borrow(r);
            resultingOwnership := OwnershipBorrowed;
          }
          readIdents := {name};
          return;
        }
        case Companion(path) => {
          var p := GenPath(path);
          r := R.RawExpr(p);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case InitializationValue(typ) => {
          var typExpr := GenType(typ, false, false);
          r := R.RawExpr("<" + typExpr.ToString(IND) + " as std::default::Default>::default()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Tuple(values) => {
          var s := "(";
          readIdents := {};

          var i := 0;
          while i < |values| {
            if i > 0 {
              s := s + " ";
            }

            var recursiveGen, _, recIdents := GenExpr(values[i], selfIdent, params, OwnershipOwned);

            s := s + recursiveGen.ToString(IND) + ",";
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + ")";
          r := R.RawExpr(s);

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
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
            s := s + R.TypeApp(R.TIdentifier("::"), typeExprs).ToString(IND);
          }
          s := s + "::new(";
          readIdents := {};
          var i := 0;
          while i < |args| {
            if i > 0 {
              s := s + ", ";
            }

            var recursiveGen, _, recIdents := GenExpr(args[i], selfIdent, params, OwnershipOwned);
            s := s + recursiveGen.ToString(IND);
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + "))";
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case NewArray(dims, typ) => {
          var i := |dims| - 1;
          var genTyp := GenType(typ, false, false);
          // TODO (Mikael): Prevent arrays from being initialized without initialization code
          var s := "<" + genTyp.ToString(IND) + " as ::std::default::Default>::default()";
          readIdents := {};
          while i >= 0 {
            var recursiveGen, _, recIdents := GenExpr(dims[i], selfIdent, params, OwnershipOwned);

            s := "::std::rc::Rc::new(::std::cell::RefCell::new(vec![" + s + "; <usize as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()]))";
            readIdents := readIdents + recIdents;

            i := i - 1;
          }

          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
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
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, [], OwnershipOwned);

              readIdents := readIdents + recIdents;
              var allReadCloned := "";
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned + "let " + escapeIdent(next) + " = " + escapeIdent(next) + ".clone();\n";
                recIdents := recIdents - {next};
              }
              s := s + escapeIdent(name) + ": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n" + allReadCloned + "move || (" + recursiveGen.ToString(IND) + ")})))";
            } else {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, params, OwnershipOwned);

              s := s + escapeIdent(name) + ": " + "(" + recursiveGen.ToString(IND) + ")";
              readIdents := readIdents + recIdents;
            }
            i := i + 1;
          }
          s := s + " })";

          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Convert(_, _, _) => {
          r, resultingOwnership, readIdents :=
            GenExprConvert(e, selfIdent, params, expectedOwnership);
        }
        case SeqConstruct(length, expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
          var lengthGen, _, lengthIdents := GenExpr(length, selfIdent, params, OwnershipOwned);

          r := R.RawExpr("{\nlet _initializer = " + recursiveGen.ToString(IND) + ";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), " + lengthGen.ToString(IND) + ").map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}");

          readIdents := recIdents + lengthIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SeqValue(exprs, typ) => {
          readIdents := {};

          var genTpe := GenType(typ, false, false);

          var i := 0;
          var args := [];
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, params, OwnershipOwned);
            readIdents := readIdents + recIdents;
            args := args + [recursiveGen];

            i := i + 1;
          }
          r := R.dafny_runtime.MSel("seq!").Apply([], args);
          if |args| == 0 {
            r := R.TypeAscription(r,
                                  R.dafny_runtime_type.MSel("Sequence").Apply1(genTpe));
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, params, OwnershipOwned);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("set!").Apply([], generatedValues);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MultisetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, params, OwnershipOwned);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("multiset!").Apply([], generatedValues);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case ToMultiset(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipAutoBorrowed);
          r := recursiveGen.Sel("as_dafny_multiset").Apply([], []);
          readIdents := recIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValue(mapElems) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |mapElems| {
            var recursiveGenKey, _, recIdentsKey := GenExpr(mapElems[i].0, selfIdent, params, OwnershipOwned);
            var recursiveGenValue, _, recIdentsValue := GenExpr(mapElems[i].1, selfIdent, params, OwnershipOwned);

            generatedValues := generatedValues + [(recursiveGenKey, recursiveGenValue)];
            readIdents := readIdents + recIdentsKey + recIdentsValue;
            i := i + 1;
          }

          i := 0;
          var arguments := [];
          while i < |generatedValues| {
            var genKey := generatedValues[i].0;
            var genValue := generatedValues[i].1;

            arguments := arguments + [R.BinaryOp("=>", genKey, genValue, DAST.Format.BinaryOpFormat.NoFormat())];
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("map!").Apply([],
                                                  arguments
          );
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SeqUpdate(expr, index, value) => {
          var exprR, _, exprIdents := GenExpr(expr, selfIdent, params, OwnershipAutoBorrowed);
          var indexR, indexOwnership, indexIdents := GenExpr(index, selfIdent, params, OwnershipBorrowed);
          var valueR, valueOwnership, valueIdents := GenExpr(value, selfIdent, params, OwnershipBorrowed);
          r := exprR.Sel("update_index").Apply([], [indexR, valueR]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := exprIdents + indexIdents + valueIdents;
          return;
        }
        case MapUpdate(expr, index, value) => {
          var exprR, _, exprIdents := GenExpr(expr, selfIdent, params, OwnershipAutoBorrowed);
          var indexR, indexOwnership, indexIdents := GenExpr(index, selfIdent, params, OwnershipBorrowed);
          var valueR, valueOwnership, valueIdents := GenExpr(value, selfIdent, params, OwnershipBorrowed);
          r := exprR.Sel("update_index").Apply([], [indexR, valueR]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := exprIdents + indexIdents + valueIdents;
          return;
        }
        case This() => {
          match selfIdent {
            case Some(id) => {
              r := R.RawExpr(id);
              if expectedOwnership == OwnershipOwned {
                r := R.Clone(r);
                resultingOwnership := OwnershipOwned;
              } else if expectedOwnership == OwnershipBorrowed || expectedOwnership == OwnershipAutoBorrowed {
                if id != "self" {
                  r := R.Borrow(r);
                }
                resultingOwnership := OwnershipBorrowed;
              } else {
                assert expectedOwnership == OwnershipBorrowedMut;
                if id != "self" {
                  r := R.BorrowMut(r);
                }
                resultingOwnership := OwnershipBorrowedMut;
              }

              readIdents := {id};
            }
            case None => {
              r := R.RawExpr("panic!(\"this outside of a method\")");
              r, resultingOwnership := FromOwned(r, expectedOwnership);
              readIdents := {};
            }
          }
          return;
        }
        case Ite(cond, t, f) => {
          assert {:split_here} true;
          var cond, _, recIdentsCond := GenExpr(cond, selfIdent, params, OwnershipOwned);
          var condString := cond.ToString(IND);

          var _, tHasToBeOwned, _ := GenExpr(t, selfIdent, params, expectedOwnership); // check if t has to be owned even if not requested
          var fExpr, fOwned, recIdentsF := GenExpr(f, selfIdent, params, tHasToBeOwned);
          var fString := fExpr.ToString(IND);
          var tExpr, _, recIdentsT := GenExpr(t, selfIdent, params, fOwned); // there's a chance that f forced ownership
          var tString := tExpr.ToString(IND);

          r := R.RawExpr("(if " + condString + " {\n" + tString + "\n} else {\n" + fString + "\n})");

          r, resultingOwnership := FromOwnership(r, fOwned, expectedOwnership);
          readIdents := recIdentsCond + recIdentsT + recIdentsF;
          return;
        }
        case UnOp(Not, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, params, OwnershipOwned);

          r := R.UnaryOp("!", recursiveGen, format);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case UnOp(BitwiseNot, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, params, OwnershipOwned);

          r := R.UnaryOp("~", recursiveGen, format);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case UnOp(Cardinality, e, format) => {
          var recursiveGen, recOwned, recIdents := GenExpr(e, selfIdent, params, OwnershipAutoBorrowed);

          r := recursiveGen.Sel("cardinality").Apply([], []);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case BinOp(_, _, _, _) =>
          r, resultingOwnership, readIdents :=
            GenExprBinary(e, selfIdent, params, expectedOwnership);
        case ArrayLen(expr, dim) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);

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
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case MapKeys(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
          readIdents := recIdents;
          r := R.Call(recursiveGen.Sel("keys"), [], []);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValues(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, params, OwnershipOwned);
          readIdents := recIdents;
          r := R.Call(recursiveGen.Sel("values"), [], []);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SelectFn(on, field, isDatatype, isStatic, arity) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, OwnershipBorrowed);
          var s: string;
          var onString := onExpr.ToString(IND);

          if isStatic {
            s := onString + "::" + escapeIdent(field);
          } else {
            s := "{\n";
            s := s + "let callTarget = (" + onString + (if onOwned == OwnershipOwned then ")" else ").clone()") + ";\n";
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
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Select(Companion(c), field, isConstant, isDatatype) => {
          var onExpr, onOwned, recIdents := GenExpr(Companion(c), selfIdent, params, OwnershipBorrowed);

          r := R.RawExpr(onExpr.ToString(IND) + "::" + escapeIdent(field) + "()");

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Select(on, field, isConstant, isDatatype) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, OwnershipBorrowed);
          if isDatatype || isConstant {
            r := R.Call(onExpr.Sel(escapeIdent(field)), [], []);
            r, resultingOwnership := FromOwned(r, expectedOwnership);
          } else {
            var s: string;
            s := "::std::ops::Deref::deref(&((" + onExpr.ToString(IND) + ")" + "." + escapeIdent(field) + ".borrow()))";
            r, resultingOwnership := FromOwnership(R.RawExpr(s), OwnershipBorrowed, expectedOwnership);
          }
          readIdents := recIdents;
          return;
        }
        case Index(on, collKind, indices) => {
          assert {:split_here} true;
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := onExpr;

          var i := 0;
          while i < |indices| {
            if collKind == CollKind.Array {
              r := r.Sel("borrow").Apply([], []);
            }
            var idx, idxOwned, recIdentsIdx := GenExpr(indices[i], selfIdent, params, OwnershipBorrowed);
            r := r.Sel("get").Apply1(idx);
            readIdents := readIdents + recIdentsIdx;
            i := i + 1;
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case IndexRange(on, isArray, low, high) => {
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, params, OwnershipAutoBorrowed);
          readIdents := recIdents;

          var methodName := if low.Some? then
            if high.Some? then "slice" else "drop"
          else if high.Some? then "take" else "";

          var arguments := [];
          match low {
            case Some(l) => {
              var lExpr, _, recIdentsL := GenExpr(l, selfIdent, params, OwnershipBorrowed);
              arguments := arguments + [lExpr];
              readIdents := readIdents + recIdentsL;
            }
            case None => {}
          }

          match high {
            case Some(h) => {
              var hExpr, _, recIdentsH := GenExpr(h, selfIdent, params, OwnershipBorrowed);
              arguments := arguments + [hExpr];
              readIdents := readIdents + recIdentsH;
            }
            case None => {}
          }

          r := onExpr;
          if isArray {
            if methodName != "" {
              methodName := "_" + methodName;
            }
            r := R.dafny_runtime_Sequence.MSel("from_array"+methodName).Apply([], arguments);
          } else {
            if methodName != "" {
              r := r.Sel(methodName).Apply([], arguments);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case TupleSelect(on, idx) => {
          var onExpr, onOwnership, recIdents := GenExpr(on, selfIdent, params, OwnershipAutoBorrowed);
          r := onExpr.Sel(Strings.OfNat(idx));
          r, resultingOwnership := FromOwnership(r, onOwnership, expectedOwnership);
          readIdents := recIdents;
          return;
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
            var argExpr, argOwnership, argIdents := GenExpr(args[i], selfIdent, params, OwnershipBorrowed);
            argExprs := argExprs + [argExpr];
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var onExpr, _, recIdents := GenExpr(on, selfIdent, params, OwnershipAutoBorrowed);
          readIdents := readIdents + recIdents;
          var renderedName := match name {
            case Name(ident) => escapeIdent(ident)
            case MapBuilderAdd | SetBuilderAdd => "add"
            case MapBuilderBuild | SetBuilderBuild => "build"
          };
          match on {
            case Companion(_) => {
              onExpr := onExpr.MSel(renderedName);
            }
            case _ => {
              onExpr := onExpr.Sel(renderedName);
            }
          }

          r := R.Call(onExpr, typeExprs, argExprs);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
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
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
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

            var valueGen, _, recIdents := GenExpr(values[i].1, selfIdent, params, OwnershipOwned);
            s := s + "let " + escapeIdent(values[i].0.name) + ": " + typStr.ToString(IND) + " = ";
            readIdents := readIdents + recIdents;

            s := s + valueGen.ToString(IND) + ";\n";
            i := i + 1;
          }

          var recGen, recOwned, recIdents := GenExpr(expr, selfIdent, paramNames, expectedOwnership);
          readIdents := recIdents - paramNamesSet;

          s := s  + recGen.ToString(IND) + "\n}";
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
          return;
        }
        case IIFE(name, tpe, value, iifeBody) => {
          var valueGen, _, recIdents := GenExpr(value, selfIdent, params, OwnershipOwned);

          readIdents := recIdents;
          var valueTypeGen := GenType(tpe, false, true);
          var bodyGen, _, bodyIdents := GenExpr(iifeBody, selfIdent, params, OwnershipOwned);
          readIdents := readIdents + (bodyIdents - {name.id});

          r := R.RawExpr("{\nlet " + escapeIdent(name.id) + ": " + valueTypeGen.ToString(IND) + " = " + valueGen.ToString(IND) + ";\n" + bodyGen.ToString(IND) + "\n}");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Apply(func, args) => {
          var funcExpr, _, recIdents := GenExpr(func, selfIdent, params, OwnershipBorrowed);
          readIdents := recIdents;

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, argOwned, argIdents := GenExpr(args[i], selfIdent, params, OwnershipBorrowed);
            var argExprString := argExpr.ToString(IND);
            if argOwned == OwnershipOwned {
              argExprString := "&" + argExprString;
            }

            argString := argString + argExprString;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          r := R.RawExpr("((" + funcExpr.ToString(IND) + ").0" + "(" + argString + "))");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case TypeTest(on, dType, variant) => {
          var exprGen, _, recIdents := GenExpr(on, selfIdent, params, OwnershipBorrowed);
          var dTypePath := GenPath(dType);
          r := R.RawExpr("matches!(" + exprGen.ToString(IND) + ".as_ref(), " + dTypePath + "::" + escapeIdent(variant) + "{ .. })");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case BoolBoundedPool() => {
          r := R.RawExpr("[false, true]");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, params, OwnershipBorrowed);
          r := R.RawExpr("(" + exprGen.ToString(IND) + ").iter()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case SeqBoundedPool(of, includeDuplicates) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, params, OwnershipBorrowed);
          var s := "(" + exprGen.ToString(IND) + ").iter()";
          if !includeDuplicates {
            s := "::dafny_runtime::itertools::Itertools::unique(" + s + ")";
          }
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case IntRange(lo, hi) => {
          var lo, _, recIdentsLo := GenExpr(lo, selfIdent, params, OwnershipOwned);
          var hi, _, recIdentsHi := GenExpr(hi, selfIdent, params, OwnershipOwned);

          r := R.RawExpr("::dafny_runtime::integer_range(" + lo.ToString(IND) + ", " + hi.ToString(IND) + ")");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdentsLo + recIdentsHi;
          return;
        }
        case MapBuilder(keyType, valueType) => {
          var kType := GenType(keyType, false, false);
          var vType := GenType(valueType, false, false);
          r := R.RawExpr("::dafny_runtime::MapBuilder::<" + kType.ToString(IND) + ", " + vType.ToString(IND) + ">::new()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBuilder(elemType) => {
          var eType := GenType(elemType, false, false);
          readIdents := {};
          r := R.RawExpr("::dafny_runtime::SetBuilder::<" + eType.ToString(IND) + ">::new()");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
      }
    }

    method Compile(p: seq<Module>) returns (s: string) {
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
