/// Utility functions for manipulating AST elements
///
/// author: Aleksandar Milicevic (t-alekm@microsoft.com)

module AstUtils

open Ast
open Utils

// ------------------------------- Visitor Stuff -------------------------------------------

let rec VisitExpr visitorFunc expr acc =
  match expr with
  | IntLiteral(_)
  | IdLiteral(_)
  | Star                   -> acc |> visitorFunc expr
  | Dot(e, _)              -> acc |> visitorFunc expr |> VisitExpr visitorFunc e
  | SelectExpr(e1, e2)     -> acc |> visitorFunc expr |> VisitExpr visitorFunc e1 |> VisitExpr visitorFunc e2
  | UpdateExpr(e1, e2, e3) -> acc |> visitorFunc expr |> VisitExpr visitorFunc e1 |> VisitExpr visitorFunc e2 |> VisitExpr visitorFunc e3
  | SequenceExpr(exs)      -> exs |> List.fold (fun acc2 e -> acc2 |> VisitExpr visitorFunc e) (visitorFunc expr acc)
  | SeqLength(e)           -> acc |> visitorFunc expr |> VisitExpr visitorFunc e
  | ForallExpr(_,e)        -> acc |> visitorFunc expr |> VisitExpr visitorFunc e
  | UnaryExpr(_,e)         -> acc |> visitorFunc expr |> VisitExpr visitorFunc e
  | BinaryExpr(_,_,e1,e2)  -> acc |> visitorFunc expr |> VisitExpr visitorFunc e1 |> VisitExpr visitorFunc e2

// ------------------------------- End Visitor Stuff -------------------------------------------

exception EvalFailed 

let rec EvalSym expr = 
  match expr with
  | IntLiteral(n) -> IntConst(n)
  | IdLiteral(id) -> VarConst(id)
  | Dot(e, str) -> 
      match EvalSym e with
      | VarConst(lhsName) -> VarConst(lhsName + "." + str)
      | _ -> ExprConst(expr)
  | SeqLength(e) -> 
      match EvalSym e with
      | SeqConst(clist) -> IntConst(List.length clist)
      | _ -> ExprConst(expr)
  | SequenceExpr(elist) -> 
      let clist = elist |> List.fold (fun acc e -> EvalSym e :: acc) [] |> List.rev |> Utils.ConvertToOptionList
      SeqConst(clist)
  | SelectExpr(lst, idx) ->
      match EvalSym lst, EvalSym idx with
      | SeqConst(clist), IntConst(n) -> clist.[n] |> Utils.ExtractOption
      | _ -> ExprConst(expr)
  | UpdateExpr(lst,idx,v) ->
      match EvalSym lst, EvalSym idx, EvalSym v with
      | SeqConst(clist), IntConst(n), (_ as c) -> SeqConst(Utils.ListSet n (Some(c)) clist)
      | _ -> ExprConst(expr)
  | BinaryExpr(_,op,e1,e2) ->
      match op with
      | Exact "=" _ ->
          match EvalSym e1, EvalSym e2 with
          | BoolConst(b1), BoolConst(b2) -> BoolConst(b1 = b2)
          | IntConst(n1), IntConst(n2)   -> BoolConst(n1 = n2)
          | VarConst(v1), VarConst(v2)   -> BoolConst(v1 = v2)
          | _ -> ExprConst(expr)
      | Exact "!=" _ -> 
          match EvalSym e1, EvalSym e2 with
          | BoolConst(b1), BoolConst(b2) -> BoolConst(not (b1 = b2))
          | IntConst(n1), IntConst(n2)   -> BoolConst(not (n1 = n2))
          | VarConst(v1), VarConst(v2)   -> BoolConst(not (v1 = v2))
          | _ -> ExprConst(expr)
      | Exact "<" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2)   -> BoolConst(n1 < n2)
          | SetConst(s1), SetConst(s2)   -> BoolConst((Set.count s1) < (Set.count s2))
          | SeqConst(s1), SeqConst(s2)   -> BoolConst((List.length s1) < (List.length s2))
          | _ -> ExprConst(expr)
      | Exact "<=" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2)   -> BoolConst(n1 <= n2)
          | SetConst(s1), SetConst(s2)   -> BoolConst((Set.count s1) <= (Set.count s2))
          | SeqConst(s1), SeqConst(s2)   -> BoolConst((List.length s1) <= (List.length s2))
          | _ -> ExprConst(expr)
      | Exact ">" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2)   -> BoolConst(n1 > n2)
          | SetConst(s1), SetConst(s2)   -> BoolConst((Set.count s1) > (Set.count s2))
          | SeqConst(s1), SeqConst(s2)   -> BoolConst((List.length s1) > (List.length s2))
          | _ -> ExprConst(expr)
      | Exact ">=" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2)   -> BoolConst(n1 >= n2)
          | SetConst(s1), SetConst(s2)   -> BoolConst((Set.count s1) >= (Set.count s2))
          | SeqConst(s1), SeqConst(s2)   -> BoolConst((List.length s1) >= (List.length s2))
          | _ -> ExprConst(expr)
      | Exact "in" _ -> 
          match EvalSym e1, EvalSym e2 with
          | _ as c, SetConst(s)   -> BoolConst(Set.contains (Some(c)) s)
          | _ as c, SeqConst(s)   -> BoolConst(Utils.ListContains (Some(c)) s)
          | _ -> ExprConst(expr)
      | Exact "!in" _ -> 
          match EvalSym e1, EvalSym e2 with
          | _ as c, SetConst(s)   -> BoolConst(not (Set.contains (Some(c)) s))
          | _ as c, SeqConst(s)   -> BoolConst(not (Utils.ListContains (Some(c)) s))
          | _ -> ExprConst(expr)
      | Exact "+" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2) -> IntConst(n1 + n2)
          | SeqConst(l1), SeqConst(l2) -> SeqConst(List.append l1 l2)
          | SetConst(s1), SetConst(s2) -> SetConst(Set.union s1 s2)
          | _ -> ExprConst(expr)
      | Exact "-" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2) -> IntConst(n1 + n2)
          | SetConst(s1), SetConst(s2) -> SetConst(Set.difference s1 s2)
          | _ -> ExprConst(expr)
      | Exact "*" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2) -> IntConst(n1 * n2)
          | _ -> ExprConst(expr)
      | Exact "div" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2) -> IntConst(n1 / n2)
          | _ -> ExprConst(expr)
      | Exact "mod" _ -> 
          match EvalSym e1, EvalSym e2 with
          | IntConst(n1), IntConst(n2) -> IntConst(n1 % n2)
          | _ -> ExprConst(expr)
      | _ -> ExprConst(expr)
  | UnaryExpr(op, e) ->
      match op with
      | Exact "!" _ -> 
          match EvalSym e with
          | BoolConst(b) -> BoolConst(not b)
          | _ -> ExprConst(expr)
      | Exact "-" _ -> 
          match EvalSym e with
          | IntConst(n) -> IntConst(-n)
          | _ -> ExprConst(expr)
      | _ -> ExprConst(expr)
  | _ -> ExprConst(expr)

//TODO: stuff might be missing
let rec EvalToConst expr = 
  match expr with
  | IntLiteral(n) -> IntConst(n)
  | IdLiteral(id) -> raise EvalFailed //VarConst(id)
  | Dot(e, str)   -> raise EvalFailed
  | SeqLength(e) -> 
      match EvalToConst e with
      | SeqConst(clist) -> IntConst(List.length clist)
      | _ -> raise EvalFailed
  | SequenceExpr(elist) -> 
      let clist = elist |> List.fold (fun acc e -> EvalToConst e :: acc) [] |> List.rev |> Utils.ConvertToOptionList
      SeqConst(clist)
  | SelectExpr(lst, idx) ->
      match EvalToConst lst, EvalToConst idx with
      | SeqConst(clist), IntConst(n) -> clist.[n] |> Utils.ExtractOption
      | _ -> raise EvalFailed
  | UpdateExpr(lst,idx,v) ->
      match EvalToConst lst, EvalToConst idx, EvalToConst v with
      | SeqConst(clist), IntConst(n), (_ as c) -> SeqConst(Utils.ListSet n (Some(c)) clist)
      | _ -> raise EvalFailed
  | BinaryExpr(_,op,e1,e2) ->
      match op with
      | Exact "=" _ ->
          try 
            BoolConst(EvalToBool(e1) = EvalToBool(e2))
          with 
          | EvalFailed -> BoolConst(EvalToInt(e1) = EvalToInt(e2))
      | Exact "!=" _ -> 
          try 
            BoolConst(not(EvalToBool(e1) = EvalToBool(e2)))
          with 
          | EvalFailed -> BoolConst(not(EvalToInt e1 = EvalToInt e2))
      | Exact "<" _ -> BoolConst(EvalToInt e1 < EvalToInt e2) //TODO sets, seqs
      | Exact "<=" _ -> BoolConst(EvalToInt e1 <= EvalToInt e2) //TODO sets, seqs
      | Exact ">" _ -> BoolConst(EvalToInt e1 > EvalToInt e2) //TODO sets, seqs
      | Exact ">=" _ -> BoolConst(EvalToInt e1 >= EvalToInt e2) //TODO sets, seqs
      | Exact "in" _ -> raise EvalFailed //TODO
      | Exact "!in" _ -> raise EvalFailed //TODO
      | Exact "+" _ -> 
          match EvalToConst e1, EvalToConst e2 with
          | IntConst(n1), IntConst(n2) -> IntConst(n1 + n2)
          | SeqConst(l1), SeqConst(l2) -> SeqConst(List.append l1 l2)
          | SetConst(s1), SetConst(s2) -> SetConst(Set.union s1 s2)
          | _ -> raise EvalFailed
      | Exact "-" _ -> IntConst(EvalToInt e1 - EvalToInt e2)
      | Exact "*" _ -> IntConst(EvalToInt e1 * EvalToInt e2)
      | Exact "div" _ -> IntConst(EvalToInt e1 / EvalToInt e2)
      | Exact "mod" _ -> IntConst(EvalToInt e1 % EvalToInt e2)
      | _ -> raise EvalFailed 
  | UnaryExpr(op, e) ->
      match op with
      | Exact "!" _ -> BoolConst(not (EvalToBool e))
      | Exact "-" _ -> IntConst(-(EvalToInt e))
      | _ -> raise EvalFailed  
  | _ -> raise EvalFailed
and EvalToBool e =
  let c = EvalToConst e
  match c with
  | BoolConst(b) -> b
  | _ -> raise EvalFailed
and EvalToInt e = 
  let c = EvalToConst e
  match c with
  | IntConst(n) -> n
  | _ -> raise EvalFailed
  
let rec Const2Expr c =
  match c with
  | IntConst(n) -> IntLiteral(n)
  | BoolConst(b) -> if b then IntLiteral(1) else IntLiteral(0) //?? BoolLiteral(b)
  | SeqConst(clist) -> 
      let expList = clist |> List.fold (fun acc c -> Const2Expr (Utils.ExtractOption c) :: acc) [] |> List.rev
      SequenceExpr(expList)
  | ThisConst(_) -> IdLiteral("this")
  | VarConst(v) -> IdLiteral(v)
  | NullConst -> IdLiteral("null")
  | ExprConst(e) -> e
  | _ -> failwith "not implemented or not supported"

//  =======================================================================
/// Returns a binary AND of the two given expressions with short-circuiting
//  =======================================================================
let BinaryAnd (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> rhs
    | IdLiteral("false"), _ -> IdLiteral("false")
    | _, IdLiteral("true")  -> lhs
    | _, IdLiteral("false") -> IdLiteral("false")
    | _, _                  -> BinaryExpr(30, "&&", lhs, rhs)

//  =======================================================================
/// Returns a binary OR of the two given expressions with short-circuiting
//  =======================================================================
let BinaryOr (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> IdLiteral("true")
    | IdLiteral("false"), _ -> rhs
    | _, IdLiteral("true")  -> IdLiteral("true")
    | _, IdLiteral("false") -> lhs
    | _, _                  -> BinaryExpr(30, "||", lhs, rhs)

//  ===================================================================================
/// Returns a binary IMPLIES of the two given expressions (TODO: with short-circuiting)
//  ===================================================================================
let BinaryImplies lhs rhs = BinaryExpr(20, "==>", lhs, rhs)

//  =================================================
/// Returns a binary NEQ of the two given expressions
//  =================================================
let BinaryNeq lhs rhs = BinaryExpr(40, "!=", lhs, rhs)

//  =================================================
/// Returns a binary EQ of the two given expressions
//  =================================================
let BinaryEq lhs rhs = BinaryExpr(40, "=", lhs, rhs)

//  =====================
/// Returns TRUE literal
//  =====================
let TrueLiteral = IdLiteral("true")

//  =====================
/// Returns FALSE literal
//  =====================
let FalseLiteral = IdLiteral("false")

//  ==========================================
/// Splits "expr" into a list of its conjuncts
//  ==========================================
let rec SplitIntoConjunts expr = 
  match expr with
  | IdLiteral("true") -> []
  | BinaryExpr(_,"&&",e0,e1) -> List.concat [SplitIntoConjunts e0 ; SplitIntoConjunts e1]
  | _ -> [expr]

//  ======================================
/// Applies "f" to each conjunct of "expr"
//  ======================================
let rec ForeachConjunct f expr =
  SplitIntoConjunts expr |> List.fold (fun acc e -> acc + (f e)) ""

// --- search functions ---
                     
//  =========================================================
/// Out of all "members" returns only those that are "Field"s                                               
//  =========================================================
let FilterFieldMembers members =
  members |> List.choose (function Field(vd) -> Some(vd) | _ -> None)

//  =============================================================
/// Out of all "members" returns only those that are constructors
//  =============================================================
let FilterConstructorMembers members = 
  members |> List.choose (function Method(_,_,_,_, true) as m -> Some(m) | _ -> None)

//  =============================================================
/// Out of all "members" returns only those that are 
/// constructors and have at least one input parameter
//  =============================================================
let FilterConstructorMembersWithParams members = 
  members |> List.choose (function Method(_,Sig(ins,outs),_,_, true) as m when not (List.isEmpty ins) -> Some(m) | _ -> None)

//  ==========================================================
/// Out of all "members" returns only those that are "Method"s
//  ==========================================================
let FilterMethodMembers members = 
  members |> List.choose (function Method(_,_,_,_,_) as m -> Some(m) | _ -> None)

//  =======================================================================
/// Returns all members of the program "prog" that pass the filter "filter"
//  =======================================================================
let FilterMembers prog filter = 
  match prog with
  | Program(components) ->
      components |> List.fold (fun acc comp -> 
        match comp with
        | Component(Class(_,_,members),_,_) -> List.concat [acc ; members |> filter |> List.choose (fun m -> Some(comp, m))]            
        | _ -> acc) []

//  =================================
/// Returns all fields of a component
//  =================================
let GetAllFields comp = 
  match comp with
  | Component(Class(_,_,members), Model(_,_,cVars,_,_), _) ->
      let aVars = FilterFieldMembers members
      List.concat [aVars ; cVars]
  | _ -> []
                    
//  =================================
/// Returns class name of a component
//  =================================
let GetClassName comp =
  match comp with
  | Component(Class(name,_,_),_,_) -> name
  | _ -> failwith ("unrecognized component: " + comp.ToString())

//  ========================
/// Returns name of a method
//  ========================
let GetMethodName mthd = 
  match mthd with
  | Method(name,_,_,_,_) -> name
  | _ -> failwith ("not a method: " + mthd.ToString())

//  ===========================================================
/// Returns full name of a method (= <class_name>.<method_name>
//  ===========================================================
let GetMethodFullName comp mthd = 
  (GetClassName comp) + "." + (GetMethodName mthd)

//  =============================
/// Returns signature of a method
//  =============================
let GetMethodSig mthd = 
  match mthd with
  | Method(_,sgn,_,_,_) -> sgn
  | _ -> failwith ("not a method: " + mthd.ToString())

//  =========================================================
/// Returns all arguments of a method (both input and output)
//  =========================================================
let GetMethodArgs mthd = 
  match mthd with
  | Method(_,Sig(ins, outs),_,_,_) -> List.concat [ins; outs]
  | _ -> failwith ("not a method: " + mthd.ToString())

//  ==============================================================
/// Returns all invariants of a component as a list of expressions
//  ==============================================================
let GetInvariantsAsList comp = 
  match comp with
  | Component(Class(_,_,members), Model(_,_,_,_,inv), _) -> 
      let clsInvs = members |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
      List.append (SplitIntoConjunts inv) clsInvs
  | _ -> failwith ("unexpected kinf of component: %s" + comp.ToString())

//  ==================================
/// Returns all members of a component
//  ==================================
let GetMembers comp =
  match comp with
  | Component(Class(_,_,members),_,_) -> members
  | _ -> failwith ("unrecognized component: " + comp.ToString())

//  ====================================================
/// Finds a component of a program that has a given name
//  ====================================================
let FindComponent (prog: Program) clsName = 
  match prog with
  | Program(comps) -> comps |> List.filter (function Component(Class(name,_,_),_,_) when name = clsName -> true | _ -> false)
                            |> Utils.ListToOption

//  ===================================================
/// Finds a method of a component that has a given name
//  ===================================================
let FindMethod comp methodName =
  let x = GetMembers comp
  let y = x |> FilterMethodMembers
  let z = y |> List.filter (function Method(name,_,_,_,_) when name = methodName -> true | _ -> false)
  GetMembers comp |> FilterMethodMembers |> List.filter (function Method(name,_,_,_,_) when name = methodName -> true | _ -> false)
                                         |> Utils.ListToOption

//  ==============================================
/// Finds a field of a class that has a given name
//  ==============================================
let FindVar (prog: Program) clsName fldName =
  let copt = FindComponent prog clsName
  match copt with
  | Some(comp) -> 
      GetAllFields comp |> List.filter (function Var(name,_) when name = fldName -> true | _ -> false)
                        |> Utils.ListToOption
  | None -> None
  
//  ==========================================================
/// Desugars a given expression so that all list constructors 
/// are expanded into explicit assignments to indexed elements
//  ==========================================================
let rec Desugar expr = 
  match expr with
  | IntLiteral(_)          
  | IdLiteral(_)           
  | Star                   
  | Dot(_)                 
  | SelectExpr(_) 
  | SeqLength(_)           -> expr
  | UpdateExpr(_)          -> expr //TODO
  | SequenceExpr(exs)      -> expr //TODO
  | ForallExpr(v,e)        -> ForallExpr(v, Desugar e)
  | UnaryExpr(op,e)        -> UnaryExpr(op, Desugar e)
  | BinaryExpr(p,op,e1,e2) -> 
      let be = BinaryExpr(p, op, Desugar e1, Desugar e2)
      try
        match op with
        | Exact "=" _ ->           
            match EvalSym e1, EvalSym e2 with
            | VarConst(v), SeqConst(clist)
            | SeqConst(clist), VarConst(v) -> 
                let rec __fff lst cnt = 
                  match lst with
                  | fs :: rest -> BinaryEq (SelectExpr(IdLiteral(v), IntLiteral(cnt))) (Const2Expr (Utils.ExtractOption clist.[cnt])) :: __fff rest (cnt+1)
                  | [] -> []
                __fff clist 0 |> List.fold (fun acc e -> BinaryAnd acc e) be
            | SeqConst(cl1), SeqConst(cl2) -> 
                let rec __fff lst1 lst2 cnt = 
                  match lst1, lst2 with
                  | fs1 :: rest1, fs2 :: rest2 -> BinaryEq (Const2Expr (Utils.ExtractOption cl1.[cnt])) (Const2Expr (Utils.ExtractOption cl2.[cnt])) :: __fff rest1 rest2 (cnt+1)
                  | [], [] -> []
                  | _ -> failwith "Lists are of different sizes"
                __fff cl1 cl2 0 |> List.fold (fun acc e -> BinaryAnd acc e) be
            | _ -> be
        | _ -> be
      with
        | EvalFailed as ex -> (* printfn "%s" (ex.StackTrace.ToString());  *) be
          

let rec DesugarLst exprLst = 
  match exprLst with
  | expr :: rest -> Desugar expr :: DesugarLst rest
  | [] -> []

