//  ####################################################################
///   Utility functions for manipulating AST elements
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module AstUtils

open Ast
open Utils

// ------------------------------- Visitor Stuff -------------------------------------------

let rec VisitExpr visitorFunc expr acc =
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_)
  | VarLiteral(_)
  | IdLiteral(_)  
  | Star                             -> acc |> visitorFunc expr
  | Dot(e, _)
  | ForallExpr(_,e)                  
  | UnaryExpr(_,e)                   
  | SeqLength(e)                     -> acc |> visitorFunc expr |> VisitExpr visitorFunc e
  | SelectExpr(e1, e2)               
  | BinaryExpr(_,_,e1,e2)            -> acc |> visitorFunc expr |> VisitExpr visitorFunc e1 |> VisitExpr visitorFunc e2
  | IteExpr(e1,e2,e3)                 
  | UpdateExpr(e1,e2,e3)             -> acc |> visitorFunc expr |> VisitExpr visitorFunc e1 |> VisitExpr visitorFunc e2 |> VisitExpr visitorFunc e3
  | SequenceExpr(exs) | SetExpr(exs) -> exs |> List.fold (fun acc2 e -> acc2 |> VisitExpr visitorFunc e) (visitorFunc expr acc)
  

// ------------------------------- End Visitor Stuff -------------------------------------------

exception EvalFailed 

let DefaultResolver e = e

let DefaultFallbackResolver resolverFunc e = 
  match resolverFunc e with
  | Some(e') -> e'
  | None -> e

let EvalSym resolverFunc expr = 
  let rec __EvalSym ctx expr = 
    match expr with
    | IntLiteral(_)  -> expr
    | BoolLiteral(_) -> expr
    | Star           -> expr //TODO: can we do better?
    | VarLiteral(_)  -> resolverFunc expr
    | IdLiteral(_)   -> resolverFunc expr
    | Dot(_)         -> resolverFunc expr
    | SeqLength(e)   -> 
        let e' = __EvalSym ctx e
        match e' with
        | SequenceExpr(elist) -> IntLiteral(List.length elist)
        | _ -> SeqLength(e')
    | SequenceExpr(elist) -> 
        let elist' = elist |> List.fold (fun acc e -> __EvalSym ctx e :: acc) [] |> List.rev
        SequenceExpr(elist')
    | SetExpr(elist) -> 
        let eset' = elist |> List.fold (fun acc e -> Set.add (__EvalSym ctx e) acc) Set.empty
        SetExpr(Set.toList eset')
    | SelectExpr(lst, idx) ->
        let lst', idx' = __EvalSym ctx lst, __EvalSym ctx idx 
        match lst', idx' with
        | SequenceExpr(elist), IntLiteral(n) -> elist.[n] 
        | _ -> SelectExpr(lst', idx')
    | UpdateExpr(lst,idx,v) ->
        let lst', idx', v' = __EvalSym ctx lst, __EvalSym ctx idx, __EvalSym ctx v
        match lst', idx', v' with
        | SequenceExpr(elist), IntLiteral(n), _ -> SequenceExpr(Utils.ListSet n v' elist)
        | _ -> UpdateExpr(lst', idx', v')
    | IteExpr(c, e1, e2) ->
       let c', e1', e2' = __EvalSym ctx c, __EvalSym ctx e1, __EvalSym ctx e2
       match c' with
       | BoolLiteral(b) -> if b then e1' else e2'
       | _ -> IteExpr(c', e1', e2')
    | BinaryExpr(p,op,e1,e2) ->
        let e1' = __EvalSym ctx e1
        let e2' = __EvalSym ctx e2 
        let recomposed = BinaryExpr(p,op,e1',e2')
        match op with
        | "=" ->
            match e1', e2' with
            | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 = b2)
            | IntLiteral(n1), IntLiteral(n2)   -> BoolLiteral(n1 = n2)
            | _ when e1' = e2' -> BoolLiteral(true)
            | _ -> recomposed
        | "!=" -> 
            match e1', e2' with
            | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(not (b1 = b2))
            | IntLiteral(n1), IntLiteral(n2)   -> BoolLiteral(not (n1 = n2))
            | _ when e1' = e2' -> BoolLiteral(false)
            | _ -> resolverFunc expr
        | "<" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 < n2)
            | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) < (List.length s2))
            | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) < (List.length s2))
            | _ -> recomposed
        | "<=" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 <= n2)
            | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) <= (List.length s2))
            | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) <= (List.length s2))
            | _ -> recomposed
        | ">" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 > n2)
            | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) > (List.length s2))
            | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) > (List.length s2))
            | _ -> recomposed
        | ">=" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 >= n2)
            | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) >= (List.length s2))
            | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) >= (List.length s2))
            | _ -> recomposed
        | "in" -> 
            match e1', e2' with
            | _, SetExpr(s)       
            | _, SequenceExpr(s)  -> BoolLiteral(Utils.ListContains e1' s)
            | _ -> recomposed
        | "!in" -> 
            match e1', e2' with
            | _, SetExpr(s)       
            | _, SequenceExpr(s)  -> BoolLiteral(not (Utils.ListContains e1' s))
            | _ -> recomposed
        | "+" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 + n2)
            | SequenceExpr(l1), SequenceExpr(l2) -> SequenceExpr(List.append l1 l2)
            | SetExpr(s1), SetExpr(s2) -> SetExpr(Set.union (Set.ofList s1) (Set.ofList s2) |> Set.toList)
            | _ -> recomposed
        | "-" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 - n2)
            | SetExpr(s1), SetExpr(s2) -> SetExpr(Set.difference (Set.ofList s1) (Set.ofList s2) |> Set.toList)
            | _ -> recomposed
        | "*" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 * n2)
            | _ -> recomposed
        | "div" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 / n2)
            | _ -> recomposed
        | "mod" -> 
            match e1', e2' with
            | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 % n2)
            | _ -> recomposed
        | "&&" -> 
           match e1', e2' with
            | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 && b2)
            | _ -> recomposed
        | "||" -> 
           match e1', e2' with
            | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 || b2)
            | _ -> recomposed
        | "==>" -> 
           match e1', e2' with
            | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral((not b1) || b2)
            | _ -> recomposed
        | "<==>" -> 
           match e1', e2' with
            | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 = b2)
            | _ -> recomposed
        | _ -> recomposed
    | UnaryExpr(op, e) ->
        let e' = __EvalSym ctx e
        let recomposed = UnaryExpr(op, e')
        match op with
        | "!" -> 
            match e' with
            | BoolLiteral(b) -> BoolLiteral(not b)
            | _ -> recomposed
        | "-" -> 
            match e' with
            | IntLiteral(n) -> IntLiteral(-n)
            | _ -> recomposed
        | _ -> recomposed
    | ForallExpr(vars, e) -> 
        let rec PrintSep sep f list =
          match list with
          | [] -> ""
          | [a] -> f a
          | a :: more -> (f a) + sep + (PrintSep sep f more)
        let rec PrintType ty =
          match ty with
          | IntType                   -> "int"
          | BoolType                  -> "bool"
          | NamedType(id, args)       -> if List.isEmpty args then id else (PrintSep ", " (fun s -> s) args)
          | SeqType(t)                -> sprintf "seq[%s]" (PrintType t)
          | SetType(t)                -> sprintf "set[%s]" (PrintType t)
          | InstantiatedType(id,args) -> sprintf "%s[%s]" id (PrintSep ", " (fun a -> PrintType a) args)
        let PrintVarDecl vd =
          match vd with
          | Var(id,None) -> id
          | Var(id,Some(ty)) -> sprintf "%s: %s" id (PrintType ty)
        vars |> List.iter (fun v -> printfn "%s" (PrintVarDecl v))
        resolverFunc expr //TODO
  __EvalSym [] expr 

//  =======================================
/// Converts a given constant to expression
//  =======================================
let rec Const2Expr c =
  match c with
  | IntConst(n) -> IntLiteral(n)
  | BoolConst(b) -> BoolLiteral(b)
  | SeqConst(clist) -> 
      let expList = clist |> List.fold (fun acc c -> Const2Expr c :: acc) [] |> List.rev
      SequenceExpr(expList)
  | ThisConst(_) -> IdLiteral("this")
  | Unresolved(name) -> IdLiteral(name)
  | NullConst -> IdLiteral("null")
  | ExprConst(e) -> e
  | _ -> failwithf "not implemented or not supported: %O" c

let rec Expr2Const e =
  match e with
  | IntLiteral(n) -> IntConst(n)
  | BoolLiteral(b) -> BoolConst(b)
  | IdLiteral("this") -> ThisConst("this",None)
  | IdLiteral("null") -> NullConst
  | IdLiteral(id) -> Unresolved(id)
  | VarLiteral(id) -> Unresolved(id)
  | SequenceExpr(elist) -> SeqConst(elist |> List.map Expr2Const)
  | SetExpr(elist) -> SetConst(elist |> List.map Expr2Const |> Set.ofList)
  | _ -> failwithf "Not a constant: %O" e

let TryExpr2Const e =
  try 
    Some(Expr2Const e)
  with
    | ex -> None

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

//  =======================================================
/// Constructors for binary EQ/NEQ of two given expressions
//  =======================================================
let BinaryNeq lhs rhs = BinaryExpr(40, "!=", lhs, rhs)
let BinaryEq lhs rhs = BinaryExpr(40, "=", lhs, rhs)

//  =======================================================
/// Constructors for binary IN/!IN of two given expressions
//  =======================================================
let BinaryIn lhs rhs = BinaryExpr(40, "in", lhs, rhs)
let BinaryNotIn lhs rhs = BinaryExpr(40, "!in", lhs, rhs)

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

let GetClassType comp = 
  match comp with
  | Component(Class(name,typeParams,_),_,_) -> NamedType(name, typeParams)
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

let GetMethodPrePost mthd = 
  match mthd with
  | Method(_,_,pre,post,_) -> pre,post
  | _ -> failwith ("not a method: " + mthd.ToString())

//  =========================================================
/// Returns all arguments of a method (both input and output)
//  =========================================================
let GetSigVars sign = 
  match sign with
  | Sig(ins, outs) -> List.concat [ins; outs]

let GetMethodArgs mthd = 
  match mthd with
  | Method(_,Sig(ins, outs),_,_,_) -> List.concat [ins; outs]
  | _ -> failwith ("not a method: " + mthd.ToString())

let rec GetTypeShortName ty =
  match ty with
  | IntType -> "int"
  | BoolType -> "bool"
  | SetType(_) -> "set"
  | SeqType(_) -> "seq"
  | NamedType(n,_) | InstantiatedType(n,_) -> n

//  ==============================================================
/// Returns all invariants of a component as a list of expressions
//  ==============================================================
let GetInvariantsAsList comp = 
  match comp with
  | Component(Class(_,_,members), Model(_,_,_,_,inv), _) -> 
      let clsInvs = members |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
      List.append (SplitIntoConjunts inv) clsInvs
  | _ -> failwithf "unexpected kind of component: %O" comp

//  ==================================
/// Returns variable name
//  ==================================
let GetVarName var =
  match var with
  | Var(name,_) -> name

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
  | BoolLiteral(_)  
  | IdLiteral(_)   
  | VarLiteral(_)        
  | Star                   
  | Dot(_)                 
  | SelectExpr(_) 
  | SeqLength(_)           
  | UpdateExpr(_)     
  | SetExpr(_)     
  | SequenceExpr(_)        -> expr 
  | ForallExpr(v,e)        -> ForallExpr(v, Desugar e)
  | UnaryExpr(op,e)        -> UnaryExpr(op, Desugar e)
  | IteExpr(c,e1,e2)       -> IteExpr(c, Desugar e1, Desugar e2)
  | BinaryExpr(p,op,e1,e2) -> 
      let be = BinaryExpr(p, op, Desugar e1, Desugar e2)
      try
        match op with
        | "=" ->           
            match EvalSym DefaultResolver e1, EvalSym DefaultResolver e2 with
            | SequenceExpr(l1), SequenceExpr(l2) -> 
                let rec __fff lst1 lst2 cnt = 
                  match lst1, lst2 with
                  | fs1 :: rest1, fs2 :: rest2 -> BinaryEq l1.[cnt] l2.[cnt] :: __fff rest1 rest2 (cnt+1)
                  | [], [] -> []
                  | _ -> failwith "Lists are of different sizes"
                __fff l1 l2 0 |> List.fold (fun acc e -> BinaryAnd acc e) be
            | e, SequenceExpr(elist)
            | SequenceExpr(elist), e -> 
                let rec __fff lst cnt = 
                  match lst with
                  | fs :: rest -> BinaryEq (SelectExpr(e, IntLiteral(cnt))) elist.[cnt] :: __fff rest (cnt+1)
                  | [] -> []
                __fff elist 0 |> List.fold (fun acc e -> BinaryAnd acc e) be
            | _ -> be
        | _ -> be
      with
        | EvalFailed as ex -> (* printfn "%O" (ex.StackTrace);  *) be

let rec DesugarLst exprLst = 
  match exprLst with
  | expr :: rest -> Desugar expr :: DesugarLst rest
  | [] -> []

let ChangeThisReceiver receiver expr = 
  let rec __ChangeThis locals expr = 
    match expr with
    | IntLiteral(_)
    | BoolLiteral(_)                   
    | Star                             
    | VarLiteral(_)
    | IdLiteral("null")                -> expr
    | IdLiteral("this")                -> receiver
    | IdLiteral(id)                    -> if Set.contains id locals then VarLiteral(id) else __ChangeThis locals (Dot(IdLiteral("this"), id))
    | Dot(e, id)                       -> Dot(__ChangeThis locals e, id)
    | ForallExpr(vars,e)               -> let newLocals = vars |> List.map (function Var(name,_) -> name) |> Set.ofList |> Set.union locals
                                          ForallExpr(vars, __ChangeThis newLocals e)   
    | UnaryExpr(op,e)                  -> UnaryExpr(op, __ChangeThis locals e)
    | SeqLength(e)                     -> SeqLength(__ChangeThis locals e)
    | SelectExpr(e1, e2)               -> SelectExpr(__ChangeThis locals e1, __ChangeThis locals e2)
    | BinaryExpr(p,op,e1,e2)           -> BinaryExpr(p, op, __ChangeThis locals e1, __ChangeThis locals e2)
    | IteExpr(e1,e2,e3)                -> IteExpr(__ChangeThis locals e1, __ChangeThis locals e2, __ChangeThis locals e3) 
    | UpdateExpr(e1,e2,e3)             -> UpdateExpr(__ChangeThis locals e1, __ChangeThis locals e2, __ChangeThis locals e3) 
    | SequenceExpr(exs)                -> SequenceExpr(exs |> List.map (__ChangeThis locals))
    | SetExpr(exs)                     -> SetExpr(exs |> List.map (__ChangeThis locals))
  (* function body starts here *)
  __ChangeThis Set.empty expr

let rec Rewrite rewriterFunc expr =
  let __RewriteOrRecurse e =
    match rewriterFunc e with
    | Some(ee) -> ee
    | None -> Rewrite rewriterFunc e 
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_)                   
  | Star      
  | VarLiteral(_)                       
  | IdLiteral(_)                     -> match rewriterFunc expr with
                                        | Some(e) -> e
                                        | None -> expr
  | Dot(e, id)                       -> Dot(__RewriteOrRecurse e, id)
  | ForallExpr(vars,e)               -> ForallExpr(vars, __RewriteOrRecurse e)   
  | UnaryExpr(op,e)                  -> UnaryExpr(op, __RewriteOrRecurse e)
  | SeqLength(e)                     -> SeqLength(__RewriteOrRecurse e)
  | SelectExpr(e1, e2)               -> SelectExpr(__RewriteOrRecurse e1, __RewriteOrRecurse e2)
  | BinaryExpr(p,op,e1,e2)           -> BinaryExpr(p, op, __RewriteOrRecurse e1, __RewriteOrRecurse e2)
  | IteExpr(e1,e2,e3)                -> IteExpr(__RewriteOrRecurse e1, __RewriteOrRecurse e2, __RewriteOrRecurse e3) 
  | UpdateExpr(e1,e2,e3)             -> UpdateExpr(__RewriteOrRecurse e1, __RewriteOrRecurse e2, __RewriteOrRecurse e3) 
  | SequenceExpr(exs)                -> SequenceExpr(exs |> List.map __RewriteOrRecurse)
  | SetExpr(exs)                     -> SetExpr(exs |> List.map __RewriteOrRecurse)

let RewriteVars vars expr = 
  let __IdIsArg id = vars |> List.exists (function Var(name,_) -> name = id)
  Rewrite (fun e ->
             match e with 
             | IdLiteral(id) when __IdIsArg id -> Some(VarLiteral(id))
             | _ -> None) expr
              