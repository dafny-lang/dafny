//  ####################################################################
///   Utility functions for manipulating AST elements
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module AstUtils

open Ast
open Getters
open Logger
open Utils

let ThisLiteral = ObjLiteral("this")
let NullLiteral = ObjLiteral("null")

let IsLogicalOp op = [ "&&"; "||"; "==>"; "<==>" ] |> Utils.ListContains op
let IsRelationalOp op = [ "="; "!="; "<"; "<="; ">"; ">="; "in"; "!in" ] |> Utils.ListContains op     

let AreInverseOps op1 op2 = match op1, op2 with "<" , ">" | ">" , "<" | "<=", ">=" | ">=", "<=" -> true | _ -> false

let DoesImplyOp op1 op2 = 
  match op1, op2 with 
  | "<" , "!=" | ">" , "!=" -> true 
  | "=" , ">=" | "=" , "<=" -> true 
  | ">" , ">=" | "<" , "<=" -> true 
  | _ -> false
let IsCommutativeOp op = match op with "=" | "!=" -> true | _ -> false

exception ExprConvFailed of string

let Expr2Int e = 
  match e with
  | IntLiteral(n) -> n
  | _ -> raise (ExprConvFailed(sprintf "not an int but: %O" e))

let Expr2Bool e = 
  match e with
  | BoolLiteral(b) -> b
  | _ -> raise (ExprConvFailed(sprintf "not a bool but: %O" e))

let Expr2List e = 
  match e with
  | SequenceExpr(elist) -> elist
  | _ -> raise (ExprConvFailed(sprintf "not a Seq but: %O" e))

let rec MyRewrite rewriterFunc rewriteRecurseFunc expr =
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_) 
  | BoxLiteral(_)                  
  | Star      
  | VarLiteral(_) 
  | ObjLiteral(_) 
  | VarDeclExpr(_)                     
  | IdLiteral(_)                     -> match rewriterFunc expr with
                                        | Some(e) -> e
                                        | None -> expr
  | Dot(e, id)                       -> Dot(rewriteRecurseFunc e, id)
  | ForallExpr(vars,e)               -> ForallExpr(vars, rewriteRecurseFunc e)   
  | UnaryExpr(op,e)                  -> UnaryExpr(op, rewriteRecurseFunc e)
  | OldExpr(e)                       -> OldExpr(rewriteRecurseFunc e)
  | LCIntervalExpr(e)                -> LCIntervalExpr(rewriteRecurseFunc e)
  | SeqLength(e)                     -> SeqLength(rewriteRecurseFunc e)
  | SelectExpr(e1, e2)               -> SelectExpr(rewriteRecurseFunc e1, rewriteRecurseFunc e2)
  | BinaryExpr(p,op,e1,e2)           -> BinaryExpr(p, op, rewriteRecurseFunc e1, rewriteRecurseFunc e2)
  | IteExpr(e1,e2,e3)                -> IteExpr(rewriteRecurseFunc e1, rewriteRecurseFunc e2, rewriteRecurseFunc e3) 
  | UpdateExpr(e1,e2,e3)             -> UpdateExpr(rewriteRecurseFunc e1, rewriteRecurseFunc e2, rewriteRecurseFunc e3) 
  | SequenceExpr(exs)                -> SequenceExpr(exs |> List.map rewriteRecurseFunc)
  | SetExpr(exs)                     -> SetExpr(exs |> List.map rewriteRecurseFunc)
  | MethodCall(rcv,cname,mname,ins)  -> MethodCall(rewriteRecurseFunc rcv, cname, mname, ins |> List.map rewriteRecurseFunc)
  | MethodOutSelect(mth,name)        -> MethodOutSelect(rewriteRecurseFunc mth, name)
  | AssertExpr(e)                    -> AssertExpr(rewriteRecurseFunc e)
  | AssumeExpr(e)                    -> AssumeExpr(rewriteRecurseFunc e)

let rec Rewrite rewriterFunc expr = 
  let __RewriteOrRecurse e =
    match rewriterFunc e with
    | Some(ee) -> ee
    | None -> Rewrite rewriterFunc e 
  MyRewrite rewriterFunc __RewriteOrRecurse expr

// TODO: double check this!
let rec RewriteBU rewriterFunc expr = 
  let rewriteRecurseFunc e =
    RewriteBU rewriterFunc e
//    let e' = Rewrite rewriterFunc e
//    match rewriterFunc e' with
//    | Some(ee) -> ee
//    | None -> e'
  let rewriteFunc e = 
    match rewriterFunc e with
    | Some(ee) -> ee
    | None -> e
  let expr' = 
    match expr with
    | IntLiteral(_)
    | BoolLiteral(_) 
    | BoxLiteral(_)                  
    | Star      
    | VarLiteral(_) 
    | ObjLiteral(_) 
    | VarDeclExpr(_)                     
    | IdLiteral(_)                     -> expr
    | Dot(e, id)                       -> Dot(rewriteRecurseFunc e, id) 
    | ForallExpr(vars,e)               -> ForallExpr(vars, rewriteRecurseFunc e)   
    | UnaryExpr(op,e)                  -> UnaryExpr(op, rewriteRecurseFunc e)
    | OldExpr(e)                       -> OldExpr(rewriteRecurseFunc e)
    | LCIntervalExpr(e)                -> LCIntervalExpr(rewriteRecurseFunc e)
    | SeqLength(e)                     -> SeqLength(rewriteRecurseFunc e)
    | SelectExpr(e1, e2)               -> SelectExpr(rewriteRecurseFunc e1, rewriteRecurseFunc e2)
    | BinaryExpr(p,op,e1,e2)           -> BinaryExpr(p, op, rewriteRecurseFunc e1, rewriteRecurseFunc e2)
    | IteExpr(e1,e2,e3)                -> IteExpr(rewriteRecurseFunc e1, rewriteRecurseFunc e2, rewriteRecurseFunc e3) 
    | UpdateExpr(e1,e2,e3)             -> UpdateExpr(rewriteRecurseFunc e1, rewriteRecurseFunc e2, rewriteRecurseFunc e3) 
    | SequenceExpr(exs)                -> SequenceExpr(exs |> List.map rewriteRecurseFunc)
    | SetExpr(exs)                     -> SetExpr(exs |> List.map rewriteRecurseFunc)
    | MethodCall(rcv,cname,mname,ins)  -> MethodCall(rewriteRecurseFunc rcv, cname, mname, ins |> List.map rewriteRecurseFunc)
    | MethodOutSelect(mth,name)        -> MethodOutSelect(rewriteRecurseFunc mth, name)
    | AssertExpr(e)                    -> AssertExpr(rewriteRecurseFunc e)
    | AssumeExpr(e)                    -> AssumeExpr(rewriteRecurseFunc e)
  expr' |> rewriteFunc

let rec RewriteWithCtx rewriterFunc ctx expr =
  let __RewriteOrRecurse ctx e =
    match rewriterFunc ctx e with
    | Some(ee) -> ee
    | None -> RewriteWithCtx rewriterFunc ctx e 
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_) 
  | BoxLiteral(_)                  
  | Star      
  | VarLiteral(_) 
  | ObjLiteral(_) 
  | VarDeclExpr(_)                     
  | IdLiteral(_)                     -> match rewriterFunc ctx expr with
                                        | Some(e) -> e
                                        | None -> expr
  | Dot(e, id)                       -> Dot(__RewriteOrRecurse ctx e, id)
  | ForallExpr(vars,e)               -> ForallExpr(vars, __RewriteOrRecurse (ctx @ vars) e)   
  | UnaryExpr(op,e)                  -> UnaryExpr(op, __RewriteOrRecurse ctx e)
  | OldExpr(e)                       -> OldExpr(__RewriteOrRecurse ctx e)
  | LCIntervalExpr(e)                -> LCIntervalExpr(__RewriteOrRecurse ctx e)
  | SeqLength(e)                     -> SeqLength(__RewriteOrRecurse ctx e)
  | SelectExpr(e1, e2)               -> SelectExpr(__RewriteOrRecurse ctx e1, __RewriteOrRecurse ctx e2)
  | BinaryExpr(p,op,e1,e2)           -> BinaryExpr(p, op, __RewriteOrRecurse ctx e1, __RewriteOrRecurse ctx e2)
  | IteExpr(e1,e2,e3)                -> IteExpr(__RewriteOrRecurse ctx e1, __RewriteOrRecurse ctx e2, __RewriteOrRecurse ctx e3) 
  | UpdateExpr(e1,e2,e3)             -> UpdateExpr(__RewriteOrRecurse ctx e1, __RewriteOrRecurse ctx e2, __RewriteOrRecurse ctx e3) 
  | SequenceExpr(exs)                -> SequenceExpr(exs |> List.map (__RewriteOrRecurse ctx))
  | SetExpr(exs)                     -> SetExpr(exs |> List.map (__RewriteOrRecurse ctx))
  | MethodCall(rcv,cname,mname,ins)  -> MethodCall(__RewriteOrRecurse ctx rcv, cname, mname, ins |> List.map (__RewriteOrRecurse ctx))
  | MethodOutSelect(mth,name)        -> MethodOutSelect(__RewriteOrRecurse ctx mth, name)
  | AssertExpr(e)                    -> AssertExpr(__RewriteOrRecurse ctx e)
  | AssumeExpr(e)                    -> AssumeExpr(__RewriteOrRecurse ctx e)

//  ====================================================
/// Substitutes all occurences of all IdLiterals having 
/// the same name as one of the variables in "vars" with
/// VarLiterals, in "expr".
//  ====================================================
let RewriteVars vars expr = 
  let __IdIsArg id = vars |> List.exists (fun var -> GetVarName var = id)
  Rewrite (fun e ->
             match e with 
             | IdLiteral(id) when __IdIsArg id -> Some(VarLiteral(id))
             | _ -> None) expr
  
//  ================================================
/// Substitutes all occurences of e1 with e2 in expr
//  ================================================
let Substitute e1 e2 expr = 
  Rewrite (fun e ->
             if e = e1 then
               Some(e2)
             else
               None) expr

//  ================================================
/// Distributes the negation operator over 
/// arithmetic relations
//  ================================================
let rec DistributeNegation expr = 
  let __Neg op = 
    match op with
    | "="  -> Some("!=")
    | "!=" -> Some("=")
    | "<"  -> Some(">=")
    | ">"  -> Some("<=")
    | ">=" -> Some("<")
    | "<=" -> Some(">")
    | _ -> None
  Rewrite (fun e -> 
    match e with
    | UnaryExpr("!", sub) ->
        match sub with 
        | BinaryExpr(p,op,lhs,rhs) -> 
            match __Neg op with
            | Some(op') -> Some(BinaryExpr(p, op', DistributeNegation lhs, DistributeNegation rhs))
            | None -> None
        | _ -> None
    | _ -> None) expr

let rec DescendExpr visitorFunc composeFunc leafVal expr = 
  let __Compose elist =
    match elist with
    | [] -> leafVal
    | fs :: rest -> rest |> List.fold (fun acc e -> composeFunc (composeFunc acc (visitorFunc e)) (DescendExpr visitorFunc composeFunc leafVal e)) (visitorFunc fs)
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_) 
  | BoxLiteral(_)
  | Star      
  | VarLiteral(_) 
  | ObjLiteral(_)                      
  | VarDeclExpr(_)
  | IdLiteral(_)                     -> leafVal
  | AssertExpr(e)
  | AssumeExpr(e)
  | Dot(e, _)
  | ForallExpr(_,e)
  | LCIntervalExpr(e)
  | OldExpr(e)
  | UnaryExpr(_,e) 
  | MethodOutSelect(e,_)          
  | SeqLength(e)                     -> __Compose (e :: [])
  | SelectExpr(e1, e2)
  | BinaryExpr(_,_,e1,e2)            -> __Compose (e1 :: e2 :: [])
  | IteExpr(e1,e2,e3)                
  | UpdateExpr(e1,e2,e3)             -> __Compose (e1 :: e2 :: e3 :: [])
  | MethodCall(rcv,_,_,aparams)      -> __Compose (rcv :: aparams)
  | SequenceExpr(exs)                
  | SetExpr(exs)                     -> __Compose exs
              
let rec DescendExpr2 visitorFunc expr acc = 
  let newAcc = acc |> visitorFunc expr
  let __Pipe elist = elist |> List.fold (fun a e -> a |> DescendExpr2 visitorFunc e) newAcc
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_)  
  | BoxLiteral(_)                 
  | Star      
  | VarLiteral(_) 
  | ObjLiteral(_)   
  | VarDeclExpr(_)                   
  | IdLiteral(_)                     -> newAcc
  | AssertExpr(e)
  | AssumeExpr(e)
  | Dot(e, _)
  | ForallExpr(_,e)
  | LCIntervalExpr(e)
  | OldExpr(e)
  | UnaryExpr(_,e)  
  | MethodOutSelect(e,_)         
  | SeqLength(e)                     -> __Pipe (e :: [])
  | SelectExpr(e1, e2)
  | BinaryExpr(_,_,e1,e2)            -> __Pipe (e1 :: e2 :: [])
  | IteExpr(e1,e2,e3)
  | UpdateExpr(e1,e2,e3)             -> __Pipe (e1 :: e2 :: e3 :: [])
  | MethodCall(rcv,_,_,aparams)      -> __Pipe (rcv :: aparams)
  | SequenceExpr(exs)                
  | SetExpr(exs)                     -> __Pipe exs

let rec DescendExpr2BU visitorFunc expr acc = 
  let __Pipe elist = 
    let newAcc = elist |> List.fold (fun a e -> a |> DescendExpr2 visitorFunc e) acc
    newAcc |> visitorFunc expr
  match expr with
  | IntLiteral(_)
  | BoolLiteral(_)  
  | BoxLiteral(_)                 
  | Star      
  | VarLiteral(_) 
  | ObjLiteral(_)   
  | VarDeclExpr(_)                   
  | IdLiteral(_)                     -> __Pipe []
  | AssertExpr(e)
  | AssumeExpr(e)
  | Dot(e, _)
  | ForallExpr(_,e)
  | LCIntervalExpr(e)
  | OldExpr(e)
  | UnaryExpr(_,e)  
  | MethodOutSelect(e,_)         
  | SeqLength(e)                     -> __Pipe (e :: [])
  | SelectExpr(e1, e2)
  | BinaryExpr(_,_,e1,e2)            -> __Pipe (e1 :: e2 :: [])
  | IteExpr(e1,e2,e3)
  | UpdateExpr(e1,e2,e3)             -> __Pipe (e1 :: e2 :: e3 :: [])
  | MethodCall(rcv,_,_,aparams)      -> __Pipe (rcv :: aparams)
  | SequenceExpr(exs)                
  | SetExpr(exs)                     -> __Pipe exs

//TODO: if names in dafny models contain funky characters, 
//      these gensym variables might not be valid identifiers
let PrintGenSym (name: string) =
  if name.StartsWith("gensym") then
    name
  else 
    let idx = name.LastIndexOf("!")
    if idx <> -1 then
      sprintf "gensym%s" (name.Substring(idx+1))
    else
      sprintf "gensym%s" name

//  =====================
/// Returns TRUE literal
//  =====================
let TrueLiteral = BoolLiteral(true)

//  =====================
/// Returns FALSE literal
//  =====================
let FalseLiteral = BoolLiteral(false)

let UnaryNeg sub =
  match sub with
  | UnaryExpr("-", s) -> s
  | _ -> UnaryExpr("-", sub)

let UnaryNot sub =
  match sub with
  | UnaryExpr("!", s) -> s
  | BoolLiteral(b) -> BoolLiteral(not b)
  | BinaryExpr(p,"=",l,r) -> BinaryExpr(p,"!=",l,r)
  | BinaryExpr(p,"!=",l,r) -> BinaryExpr(p,"=",l,r)
  | BinaryExpr(p,"in",l,r) -> BinaryExpr(p,"!in",l,r)
  | BinaryExpr(p,"!in=",l,r) -> BinaryExpr(p,"in",l,r)
  | BinaryExpr(p,"<",l,r) -> BinaryExpr(p,">=",l,r)
  | BinaryExpr(p,"<=",l,r) -> BinaryExpr(p,">",l,r)
  | BinaryExpr(p,">",l,r) -> BinaryExpr(p,"<=",l,r)
  | BinaryExpr(p,">=",l,r) -> BinaryExpr(p,"<",l,r)
  | _ -> UnaryExpr("!", sub)

//  =======================================================================
/// Returns a binary AND of the two given expressions with short-circuiting
//  =======================================================================
let BinaryAnd (lhs: Expr) (rhs: Expr) = 
  match lhs, rhs with
  | BoolLiteral(true), _  -> rhs
  | BoolLiteral(false), _ -> FalseLiteral
  | _, BoolLiteral(true)  -> lhs
  | _, BoolLiteral(false) -> FalseLiteral
  | _, _                  -> BinaryExpr(30, "&&", lhs, rhs)

//  =======================================================================
/// Returns a binary OR of the two given expressions with short-circuiting
//  =======================================================================
let BinaryOr (lhs: Expr) (rhs: Expr) = 
  match lhs, rhs with
  | BoolLiteral(true), _  -> TrueLiteral
  | BoolLiteral(false), _ -> rhs
  | _, BoolLiteral(true)  -> TrueLiteral
  | _, BoolLiteral(false) -> lhs
  | _, _                  -> BinaryExpr(30, "||", lhs, rhs)

//  ===================================================================================
/// Returns a binary IMPLIES of the two given expressions 
//  ===================================================================================
let BinaryImplies lhs rhs = 
  match lhs, rhs with
  | BoolLiteral(false), _ -> TrueLiteral
  | BoolLiteral(true), _  -> rhs
  | _, BoolLiteral(true)  -> lhs
  | _, BoolLiteral(false) -> UnaryNot(lhs)
  | _ -> BinaryExpr(20, "==>", lhs, rhs)

//  =======================================================
/// Constructors for binary EQ/NEQ of two given expressions
//  =======================================================
let BinaryNeq lhs rhs = 
  match lhs, rhs with
  | BoolLiteral(true), x | x, BoolLiteral(true) -> UnaryNot x
  | BoolLiteral(false), x | x, BoolLiteral(false) -> x
  | _ -> BinaryExpr(40, "!=", lhs, rhs)

let BinaryEq lhs rhs = 
  match lhs, rhs with
  | BoolLiteral(true), x | x, BoolLiteral(true) -> x
  | BoolLiteral(false), x | x, BoolLiteral(false) -> UnaryNot x
  | _ when lhs = rhs -> TrueLiteral
  | _ -> BinaryExpr(40, "=", lhs, rhs)

//  =======================================================
/// Constructor for binary GETS
//  =======================================================
let BinaryGets lhs rhs = Assign(lhs, rhs)

let BinaryAdd lhs rhs = BinaryExpr(55, "+", lhs, rhs)
let BinarySub lhs rhs = BinaryExpr(55, "-", lhs, rhs)

//  =======================================================
/// Constructors for binary IN/!IN of two given expressions
//  =======================================================
let BinaryIn lhs rhs = 
  match lhs, rhs with
  | _, SequenceExpr(elist) | _, SetExpr(elist) when elist |> List.length = 0 -> FalseLiteral
  | _, SequenceExpr(elist) | _, SetExpr(elist) when elist |> List.length = 1 -> BinaryEq lhs (elist.[0])
  | _ -> BinaryExpr(40, "in", lhs, rhs)

let BinaryNotIn lhs rhs = 
  match lhs, rhs with
  | _, SequenceExpr(elist) | _, SetExpr(elist) when elist |> List.length = 0 -> TrueLiteral
  | _, SequenceExpr(elist) | _, SetExpr(elist) when elist |> List.length = 1 -> BinaryNeq lhs (elist.[0])
  | _ -> BinaryExpr(40, "!in", lhs, rhs)
  
//  ==========================================
/// Splits "expr" into a list of its conjuncts
//  ==========================================
let rec SplitIntoConjunts expr = 
  match expr with
  | BoolLiteral(true) -> []
  | BinaryExpr(_,"&&",e0,e1) -> List.concat [SplitIntoConjunts e0 ; SplitIntoConjunts e1]
  | _ -> [expr]

//  ======================================
/// Applies "f" to each conjunct of "expr"
//  ======================================
let rec ForeachConjunct f expr =
  SplitIntoConjunts expr |> List.fold (fun acc e -> acc + (f e)) ""

//  =======================================
/// Converts a given constant to expression
//  =======================================
let rec Const2Expr c =
  match c with
  | IntConst(n) -> IntLiteral(n)
  | BoolConst(b) -> BoolLiteral(b)
  | BoxConst(id) -> BoxLiteral(id)
  | SeqConst(clist) -> 
      let expList = clist |> List.fold (fun acc c -> Const2Expr c :: acc) [] |> List.rev
      SequenceExpr(expList)
  | SetConst(cset) -> 
      let expSet = cset |> Set.fold (fun acc c -> Set.add (Const2Expr c) acc) Set.empty
      SetExpr(Set.toList expSet)
  | VarConst(id) -> VarLiteral(id)
  | ThisConst(_,_) -> ObjLiteral("this")
  | NewObj(name,_) -> ObjLiteral(PrintGenSym name)
  | NullConst -> ObjLiteral("null")
  | Unresolved(id) -> BoxLiteral(id) // failwithf "don't want to convert Unresolved(%s) to expr" name // 
  | _ -> failwithf "not implemented or not supported: %O" c

let rec Expr2Const e =
  match e with
  | IntLiteral(n) -> IntConst(n)
  | BoolLiteral(b) -> BoolConst(b)
  | BoxLiteral(id) -> BoxConst(id)
  | ObjLiteral("this") -> ThisConst("this",None)
  | ObjLiteral("null") -> NullConst
  | ObjLiteral(name) -> NewObj(name, None)
  | IdLiteral(id) -> Unresolved(id)
  | VarLiteral(id) -> VarConst(id)
  | SequenceExpr(elist) -> SeqConst(elist |> List.map Expr2Const)
  | SetExpr(elist) -> SetConst(elist |> List.map Expr2Const |> Set.ofList)
  | _ -> failwithf "Not a constant: %O" e

let rec Expr2ConstStrict e =
  match e with
  | IntLiteral(n) -> IntConst(n)
  | BoolLiteral(b) -> BoolConst(b)
  | BoxLiteral(id) -> BoxConst(id)
  | ObjLiteral("this") -> ThisConst("this",None)
  | ObjLiteral("null") -> NullConst
  | ObjLiteral(name) -> NewObj(name, None)
  | SequenceExpr(elist) -> SeqConst(elist |> List.map Expr2ConstStrict)
  | SetExpr(elist) -> SetConst(elist |> List.map Expr2ConstStrict |> Set.ofList)
  | _ -> failwithf "Not a constant: %O" e

let TryExpr2Const e =
  try 
    Some(Expr2Const e)
  with
    | ex -> None

let IsConstExpr e = 
  try 
    Expr2Const e |> ignore
    true
  with
    | _ -> false

///////

let GetMethodPre mthd = 
  match mthd with 
  | Method(_,_,pre,_,_) -> pre
  | _ -> failwith ("not a method" + mthd.ToString())

let GetMethodPrePost mthd = 
  let __FilterOutAssumes e = e |> SplitIntoConjunts |> List.filter (function AssumeExpr(_) -> false | _ -> true) |> List.fold BinaryAnd TrueLiteral
  match mthd with
  | Method(_,_,pre,post,_) -> __FilterOutAssumes pre,post
  | _ -> failwith ("not a method: " + mthd.ToString())

let GetMethodGhostPrecondition mthd = 
  match mthd with 
  | Method(_,_,pre,_,_) -> 
      pre |> SplitIntoConjunts |> List.choose (function AssumeExpr(e) -> Some(e) | _ -> None) |> List.fold BinaryAnd TrueLiteral
  | _ -> failwith ("not a method: " + mthd.ToString())

//  ==============================================================
/// Returns all invariants of a component as a list of expressions
//  ==============================================================
let GetInvariantsAsList comp = 
  match comp with
  | Component(Interface(_,_,members), DataModel(_,_,_,_,inv), _) -> 
      let clsInvs = members |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
      List.append (SplitIntoConjunts inv) clsInvs
  | _ -> failwithf "unexpected kind of component: %O" comp

/// Replaces all Old nodes with IdLiteral with name = "old_" + <name>
let RewriteOldExpr expr = 
  expr |> RewriteBU (fun e -> match e with
                              | OldExpr(IdLiteral(name)) -> Some(IdLiteral(RenameToOld name))
                              | _ -> None)

let MakeOldVar var = 
  match var with
  | Var(name, ty, _) -> Var(name, ty, true)

let MakeOldVars varLst =
  varLst |> List.map MakeOldVar

/// renames ALL variables to "old_"+<varname>
let MakeOld expr = 
  expr |> RewriteBU (fun e -> match e with 
                              | IdLiteral(name) when not (name="this") -> Some(IdLiteral(RenameToOld name)) 
                              | Dot(e, name) -> Some(Dot(e, RenameToOld name))
                              | _ -> None)

let BringToPost expr =
  expr |> RewriteBU (fun e -> match e with 
                              | IdLiteral(name) -> Some(IdLiteral(RenameFromOld name))
                              | Dot(e, name) -> Some(Dot(e, RenameFromOld name))
                              | _ -> None)

////////////////////////

let AddReplaceMethod prog comp newMthd oldMethod =
  match prog, comp with
  | Program(clist), Component(Interface(cname, ctypeParams, members), model, code) ->
      let newMembers = 
        match oldMethod with
        | None -> members @ [newMthd]
        | Some(m) -> Utils.ListReplace m newMthd members
      let newCls = Interface(cname, ctypeParams, newMembers)
      let newComp = Component(newCls, model, code)
      let newProg = Program(Utils.ListReplace comp newComp clist)
      newProg, newComp
  | _ -> failwithf "Invalid component: %O" comp

let UnwrapAssumes e = e |> SplitIntoConjunts |> List.map (function AssumeExpr(e) -> e | x -> x) |> List.fold BinaryAnd TrueLiteral
  
let AddPrecondition m e =
  match m with
  | Method(mn, sgn, pre, post, cstr) -> Method(mn, sgn, BinaryAnd pre (AssumeExpr(e |> UnwrapAssumes)), post, cstr)
  | _ -> failwithf "Not a method: %O" m

let SetPrecondition m e =
  match m with
  | Method(mn, sgn, pre, post, cstr) -> Method(mn, sgn, AssumeExpr(e |> UnwrapAssumes), post, cstr)
  | _ -> failwithf "Not a method: %O" m

////////////////////

exception EvalFailed of string
exception DomainNotInferred

let DefaultResolver e fldOpt = 
  match fldOpt with
  | None -> e
  | Some(fldName) -> Dot(e, fldName)

let DefaultFallbackResolver resolverFunc e = 
  match resolverFunc e with
  | Some(e') -> e'
  | None -> e

let __CheckEqual e1 e2 =
  match e1, e2 with
  | BoolLiteral(b1), BoolLiteral(b2) -> Some(b1 = b2)
  | IntLiteral(n1), IntLiteral(n2)   -> Some(n1 = n2)
  | ObjLiteral(o1), ObjLiteral(o2)   -> Some(o1 = o2)
  | SetExpr(elist1), SetExpr(elist2) -> Some(Set.ofList elist1 = Set.ofList elist2)
  | SequenceExpr(elist1), SequenceExpr(elist2) -> Some(elist1 = elist2)
  | UnaryExpr("-", sub1), sub2
  | sub1, UnaryExpr("-", sub2)                 when sub1 = sub2 -> Some(false)
  | UnaryExpr("-", sub1), UnaryExpr("-", sub2) when sub1 = sub2 -> Some(true)
  | UnaryExpr("!", sub1), sub2
  | sub1, UnaryExpr("!", sub2)                 when sub1 = sub2 -> Some(false)
  | UnaryExpr("!", sub1), UnaryExpr("-", sub2) when sub1 = sub2 -> Some(true)
  | _ when e1 = e2 -> Some(true)
  | _ -> None

let EvalSym2 fullResolverFunc otherResolverFunc returnFunc ctx expr = 
  let rec __EvalSym resolverFunc returnFunc ctx expr =
    let expr' = 
      match expr with
      | IntLiteral(_)  -> expr 
      | BoolLiteral(_) -> expr 
      | BoxLiteral(_)  -> expr 
      | ObjLiteral(_)  -> expr 
      | Star           -> expr  //TODO: can we do better?
      | VarDeclExpr(_) -> expr 
      | AssertExpr(e)  -> AssertExpr(__EvalSym resolverFunc returnFunc ctx e) 
      | AssumeExpr(e)  -> AssumeExpr(__EvalSym resolverFunc returnFunc ctx e) 
      | VarLiteral(id) -> 
          try 
            let _,e = ctx |> List.find (fun (v,e) -> GetVarName v = id)
            e 
          with 
          | ex -> resolverFunc expr None 
      | IdLiteral(_)   -> resolverFunc expr None 
      | Dot(e, str)    -> 
          let discr = __EvalSym resolverFunc returnFunc ctx e
          resolverFunc discr (Some(str)) 
      | SeqLength(e)   -> 
          let e' = __EvalSym resolverFunc returnFunc ctx e
          match e' with
          | SequenceExpr(elist) -> IntLiteral(List.length elist) 
          | _ -> SeqLength(e') 
      | SequenceExpr(elist) -> 
          let elist' = elist |> List.map (__EvalSym resolverFunc returnFunc ctx) // List.fold (fun acc e -> (__EvalSym resolverFunc returnFunc ctx e) :: acc) [] |> List.rev 
          SequenceExpr(elist') 
      | SetExpr(elist) -> 
          let elist' = elist |> List.map (__EvalSym resolverFunc returnFunc ctx) //List.fold (fun acc e -> Set.add (__EvalSym resolverFunc returnFunc ctx e) acc) Set.empty 
          SetExpr(elist' |> Set.ofList |> Set.toList) 
      | MethodOutSelect(e,name) -> 
          MethodOutSelect(__EvalSym resolverFunc returnFunc ctx e, name)
      | MethodCall(rcv,cname, mname,aparams) ->
          let rcv' = __EvalSym resolverFunc returnFunc ctx rcv
          let aparams' = aparams |> List.fold (fun acc e -> __EvalSym resolverFunc returnFunc ctx e :: acc) [] |> List.rev
          MethodCall(rcv', cname, mname, aparams') 
      | LCIntervalExpr(_) -> expr 
      | SelectExpr(lst, idx) ->
          let lst' = __EvalSym resolverFunc returnFunc ctx lst
          let idx' = __EvalSym resolverFunc returnFunc ctx idx 
          match lst', idx' with
          | SequenceExpr(elist), IntLiteral(n) -> elist.[n] 
          | SequenceExpr(elist), LCIntervalExpr(startIdx) ->
              let startIdx' = __EvalSym resolverFunc returnFunc ctx startIdx
              match startIdx' with
              | IntLiteral(startIdxInt) -> 
                  let rec __Skip n l = if n = 0 then l else __Skip (n-1) (List.tail l)
                  SequenceExpr(__Skip startIdxInt elist)
              | _ -> SelectExpr(lst', idx')
          | _ -> SelectExpr(lst', idx')
      | UpdateExpr(lst,idx,v) ->
          let lst', idx', v' = __EvalSym resolverFunc returnFunc ctx lst, __EvalSym resolverFunc returnFunc ctx idx, __EvalSym resolverFunc returnFunc ctx v
          match lst', idx', v' with
          | SequenceExpr(elist), IntLiteral(n), _ -> SequenceExpr(Utils.ListSet n v' elist)
          | _ -> UpdateExpr(lst', idx', v')
      | IteExpr(c, e1, e2) ->
          let c' = __EvalSym fullResolverFunc returnFunc ctx c
          match c' with
          | BoolLiteral(b) -> if b then __EvalSym resolverFunc returnFunc ctx e1 else __EvalSym resolverFunc returnFunc ctx e2
          | _ -> IteExpr(c', __EvalSym resolverFunc returnFunc ctx e1, __EvalSym resolverFunc returnFunc ctx e2)
      | BinaryExpr(p,op,e1,e2) ->
          let e1' = lazy (__EvalSym resolverFunc returnFunc ctx e1)
          let e2' = lazy (__EvalSym resolverFunc returnFunc ctx e2)
          let recomposed = lazy (BinaryExpr(p, op, e1'.Force(), e2'.Force()))
          match op with
          | "=" ->
              let e1'' = e1'.Force()
              let e2'' = e2'.Force()
              let eq = __CheckEqual e1'' e2''
              match eq with
              | Some(b) -> BoolLiteral(b)
              | None -> recomposed.Force()
          | "!=" -> 
              let e1'' = e1'.Force()
              let e2'' = e2'.Force()
              let eq = __CheckEqual e1'' e2''
              match eq with
              | Some(b) -> BoolLiteral(not b)
              | None -> recomposed.Force()
          | "<" -> 
              match e1'.Force(), e2'.Force() with
              | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 < n2)
              | _ -> recomposed.Force()
          | "<=" -> 
              let e1'' = e1'.Force()
              let e2'' = e2'.Force()
              let eq = __CheckEqual e1'' e2''
              match eq with
              | Some(true) -> TrueLiteral
              | _ -> match e1'', e2'' with
                     | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 <= n2)
                     | _ -> recomposed.Force()
          | ">" -> 
              match e1'.Force(), e2'.Force() with
              | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 > n2)
              | _ -> recomposed.Force()
          | ">=" -> 
              let e1'' = e1'.Force()
              let e2'' = e2'.Force()
              let eq = __CheckEqual e1'' e2''
              match eq with
              | Some(true) -> TrueLiteral
              | _ -> match e1'', e2'' with
                     | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 >= n2)
                     | _ -> recomposed.Force()
          | ".." ->
              let e1'' = e1'.Force()
              let e2'' = e2'.Force()
              match e1'', e2'' with
              | IntLiteral(lo), IntLiteral(hi)    -> SequenceExpr([lo .. hi] |> List.map (fun n -> IntLiteral(n)))
              | _ -> recomposed.Force();
          | "in" -> 
              match e1'.Force(), e2'.Force() with
              | _, SetExpr(s)       
              | _, SequenceExpr(s)  -> //BoolLiteral(Utils.ListContains (e1'.Force()) s)
                  if Utils.ListContains (e1'.Force()) s then
                    TrueLiteral
                  else
                    try 
                      let contains = s |> List.map Expr2ConstStrict |> Utils.ListContains (e1'.Force() |> Expr2ConstStrict)
                      BoolLiteral(contains)
                    with
                    | _ -> recomposed.Force()
              | _ -> recomposed.Force()
          | "!in" -> 
              match e1'.Force(), e2'.Force() with
              | _, SetExpr(s)       
              | _, SequenceExpr(s)  -> //BoolLiteral(not (Utils.ListContains (e1'.Force()) s))
                  if Utils.ListContains (e1'.Force()) s then
                    FalseLiteral
                  else
                    try 
                      let contains = s |> List.map Expr2ConstStrict |> Utils.ListContains (e1'.Force() |> Expr2ConstStrict)
                      BoolLiteral(not contains)
                    with
                    | _ -> recomposed.Force()
              | _ -> recomposed.Force()
          | "+" -> 
              let e1'' = e1'.Force();
              let e2'' = e2'.Force();
              match e1'', e2'' with
              | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 + n2)
              | SequenceExpr(l1), SequenceExpr(l2) -> SequenceExpr(List.append l1 l2)
              | SetExpr(s1), SetExpr(s2) -> SetExpr(Set.union (Set.ofList s1) (Set.ofList s2) |> Set.toList)
              | _ -> recomposed.Force()
          | "-" -> 
              match e1'.Force(), e2'.Force() with
              | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 - n2)
              | SetExpr(s1), SetExpr(s2) -> SetExpr(Set.difference (Set.ofList s1) (Set.ofList s2) |> Set.toList)
              | _ -> recomposed.Force()
          | "*" -> 
              match e1'.Force(), e2'.Force() with
              | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 * n2)
              | _ -> recomposed.Force()
          | "div" -> 
              match e1'.Force(), e2'.Force() with
              | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 / n2)
              | _ -> recomposed.Force()
          | "mod" -> 
              match e1'.Force(), e2'.Force() with
              | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 % n2)
              | _ -> recomposed.Force()
          | "&&" -> 
              // shortcircuit
              match e1'.Force() with
              | BoolLiteral(false) -> BoolLiteral(false)
              | _ ->
                  match e1'.Force(), e2'.Force() with
                  | _, BoolLiteral(false)            -> BoolLiteral(false)
                  | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 && b2)
                  | _ -> BinaryAnd (e1'.Force()) (e2'.Force())
          | "||" -> 
              // shortcircuit
              match e1'.Force() with
              | BoolLiteral(true) -> BoolLiteral(true)
              | _ ->
                  match e1'.Force(), e2'.Force() with
                  | _, BoolLiteral(true)             -> BoolLiteral(true)
                  | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 || b2)
                  | _ -> BinaryOr (e1'.Force()) (e2'.Force())
          | "==>" -> 
              // shortcircuit
              match e1'.Force() with
              | BoolLiteral(false) -> BoolLiteral(true)
              | _ ->
                  let e1'' = e1'.Force()
                  let e2'' = e2'.Force()
                  BinaryImplies e1'' e2''
          | "<==>" -> 
              match e1'.Force(), e2'.Force() with
              | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 = b2)
              | x, BoolLiteral(b)
              | BoolLiteral(b), x -> if b then x else UnaryNot(x)
              | _ -> recomposed.Force()
          | _ -> recomposed.Force()
      | OldExpr(e) ->  
          let e' = __EvalSym resolverFunc returnFunc ctx e
          let recomposed = OldExpr(e')
          match e with
          | IdLiteral(name) -> resolverFunc (IdLiteral(RenameToOld name)) None
          | _ -> recomposed
      | UnaryExpr(op, e) ->
          let e' = __EvalSym resolverFunc returnFunc ctx e
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
          let rec __ExhaustVar v restV vDomain = 
            match vDomain with
            | vv :: restD -> 
                let ctx' = (v,vv) :: ctx
                let e' = __EvalSym resolverFunc returnFunc ctx' (ForallExpr(restV, e))
                let erest = __ExhaustVar v restV restD
                BinaryAnd e' erest
            | [] -> BoolLiteral(true)
          let rec __TraverseVars vars =
            match vars with
            | v :: restV -> 
                try 
                  let vDom = GetVarDomain resolverFunc returnFunc ctx v e
                  __ExhaustVar v restV vDom
                with
                  | ex -> ForallExpr([v], __TraverseVars restV) 
            | [] -> __EvalSym resolverFunc returnFunc ctx e
          (* --- function body starts here --- *)
          __TraverseVars vars
    if expr' = FalseLiteral then
      Logger.Debug ""
    expr' |> returnFunc
  and GetVarDomain resolverFunc returnFunc ctx var expr = 
    match expr with 
    | BinaryExpr(_, "==>", lhs, rhs) -> 
        let conjs = SplitIntoConjunts lhs
        conjs |> List.fold (fun acc e ->
                              match e with
                              | BinaryExpr(_, "in", VarLiteral(vn), rhs) when GetVarName var = vn ->
                                  match __EvalSym resolverFunc returnFunc ctx rhs with
                                  | SetExpr(elist)
                                  | SequenceExpr(elist) -> elist |> List.append acc
                                  | x -> raise DomainNotInferred
                              | BinaryExpr(_, op, VarLiteral(vn),oth)
                              | BinaryExpr(_, op, oth, VarLiteral(vn)) when GetVarName var = vn && Set.ofList ["<"; "<="; ">"; ">="] |> Set.contains op -> 
                                  failwith "Not implemented yet"
                              | _ -> raise DomainNotInferred) []
    | _ -> 
        Logger.WarnLine ("unknown pattern for a quantified expression; cannot infer domain of quantified variable \"" + (GetVarName var) + "\"")
        raise DomainNotInferred
  (* --- function body starts here --- *)
  __EvalSym otherResolverFunc returnFunc ctx expr

let EvalSym resolverFunc expr = 
  EvalSym2 resolverFunc resolverFunc (fun e -> e) [] expr 

let EvalSymRet fullResolverFunc resolverFunc returnFunc expr = 
  EvalSym2 fullResolverFunc resolverFunc returnFunc [] expr 
  
//  ==========================================================
/// Desugars a given expression so that all list constructors 
/// are expanded into explicit assignments to indexed elements
//  ==========================================================
let MyDesugar expr removeOriginal =
  let rec __Desugar expr = 
    match expr with
    | IntLiteral(_)          
    | BoolLiteral(_)  
    | BoxLiteral(_)
    | VarDeclExpr(_)
    | IdLiteral(_)   
    | VarLiteral(_)        
    | ObjLiteral(_)
    | Star                   
    | Dot(_)                 
    | SelectExpr(_) 
    | SeqLength(_)           
    | UpdateExpr(_)     
    | SetExpr(_)
    | MethodCall(_)  
    | MethodOutSelect(_)   
    | SequenceExpr(_)        -> expr 
    // forall v :: v in {a1 a2 ... an} ==> e  ~~~> e[v/a1] && e[v/a2] && ... && e[v/an] 
    // forall v :: v in [a1 a2 ... an] ==> e  ~~~> e[v/a1] && e[v/a2] && ... && e[v/an] 
    | ForallExpr([Var(vn1,ty1,old1)] as v, (BinaryExpr(_, "==>", BinaryExpr(_, "in", VarLiteral(vn2), rhsCol), sub) as ee)) when vn1 = vn2 ->
        match rhsCol with 
        | SetExpr(elist)
        | SequenceExpr(elist) -> elist |> List.fold (fun acc e -> BinaryAnd acc (__Desugar (Substitute (VarLiteral(vn2)) e sub))) TrueLiteral
        | _ -> ForallExpr(v, __Desugar ee)
    | ForallExpr(v,e)        -> ForallExpr(v, __Desugar e)
    | LCIntervalExpr(e)      -> LCIntervalExpr(__Desugar e)
    | OldExpr(e)             -> OldExpr(__Desugar e)
    | UnaryExpr(op,e)        -> UnaryExpr(op, __Desugar e)
    | AssertExpr(e)          -> AssertExpr(__Desugar e)
    | AssumeExpr(e)          -> AssumeExpr(__Desugar e)
    | IteExpr(c,e1,e2)       -> IteExpr(c, __Desugar e1, __Desugar e2)
    // lst = [a1 a2 ... an] ~~~> lst = [a1 a2 ... an] && lst[0] = a1 && lst[1] = a2 && ... && lst[n-1] = an && |lst| = n
    | BinaryExpr(p,op,e1,e2) -> 
        let be = BinaryExpr(p, op, __Desugar e1, __Desugar e2)
        let fs = if removeOriginal then TrueLiteral else be
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
                  __fff l1 l2 0 |> List.fold (fun acc e -> BinaryAnd acc e) fs
              | e, SequenceExpr(elist)
              | SequenceExpr(elist), e -> 
                  let rec __fff lst cnt = 
                    match lst with
                    | fs :: rest -> BinaryEq (SelectExpr(e, IntLiteral(cnt))) elist.[cnt] :: __fff rest (cnt+1)
                    | [] -> [BinaryEq (SeqLength(e)) (IntLiteral(cnt))] 
                  __fff elist 0 |> List.fold (fun acc e -> BinaryAnd acc e) fs
              | _ -> be
          | _ -> be
        with
          | EvalFailed(_) as ex -> (* printfn "%O" (ex.StackTrace);  *) be
  __Desugar expr

let Desugar expr = MyDesugar expr false
let DesugarAndRemove expr = MyDesugar expr true

let rec DesugarLst exprLst = 
  match exprLst with
  | expr :: rest -> Desugar expr :: DesugarLst rest 
  | [] -> []

let ChangeThisReceiver receiver expr = 
  let rec __ChangeThis locals expr = 
    match expr with
    | IntLiteral(_)
    | BoolLiteral(_)       
    | BoxLiteral(_)            
    | Star   
    | VarDeclExpr(_)                          
    | VarLiteral(_)                        -> expr
    | ObjLiteral("this")                   -> receiver
    | ObjLiteral(_)                        -> expr
    | IdLiteral("null")                    -> failwith "should never happen anymore"   //TODO
    | IdLiteral("this")                    -> failwith "should never happen anymore"
    | IdLiteral(id)                        -> if Set.contains id locals then VarLiteral(id) else __ChangeThis locals (Dot(ObjLiteral("this"), id))
    | Dot(e, id)                           -> Dot(__ChangeThis locals e, id)
    | AssertExpr(e)                        -> AssertExpr(__ChangeThis locals e)
    | AssumeExpr(e)                        -> AssumeExpr(__ChangeThis locals e)
    | ForallExpr(vars,e)                   -> let newLocals = vars |> List.map GetVarName |> Set.ofList |> Set.union locals
                                              ForallExpr(vars, __ChangeThis newLocals e)   
    | LCIntervalExpr(e)                    -> LCIntervalExpr(__ChangeThis locals e)
    | OldExpr(e)                           -> OldExpr(__ChangeThis locals e)
    | UnaryExpr(op,e)                      -> UnaryExpr(op, __ChangeThis locals e)
    | SeqLength(e)                         -> SeqLength(__ChangeThis locals e)
    | SelectExpr(e1, e2)                   -> SelectExpr(__ChangeThis locals e1, __ChangeThis locals e2)
    | BinaryExpr(p,op,e1,e2)               -> BinaryExpr(p, op, __ChangeThis locals e1, __ChangeThis locals e2)
    | IteExpr(e1,e2,e3)                    -> IteExpr(__ChangeThis locals e1, __ChangeThis locals e2, __ChangeThis locals e3) 
    | UpdateExpr(e1,e2,e3)                 -> UpdateExpr(__ChangeThis locals e1, __ChangeThis locals e2, __ChangeThis locals e3) 
    | SequenceExpr(exs)                    -> SequenceExpr(exs |> List.map (__ChangeThis locals))
    | SetExpr(exs)                         -> SetExpr(exs |> List.map (__ChangeThis locals))
    | MethodOutSelect(e, name)             -> MethodOutSelect(__ChangeThis locals e, name)
    | MethodCall(rcv,cname, mname,aparams) -> MethodCall(__ChangeThis locals rcv, cname, mname, aparams |> List.map (__ChangeThis locals))
  (* --- function body starts here --- *)
  __ChangeThis Set.empty expr

let rec SimplifyExpr expr = 
  let __Simplify expr = 
    match expr with
    | UnaryExpr("!", sub) -> Some(UnaryNot sub)
    | BinaryExpr(_, "&&", l, r) -> Some(BinaryAnd l r)
    | BinaryExpr(_, "||", l, r) -> Some(BinaryOr l r)
    | BinaryExpr(_, "in", l, r) -> Some(BinaryIn l r)
    | BinaryExpr(_, "!in", l, r) -> Some(BinaryNotIn l r)
    | BinaryExpr(_, "==>", l, r) -> Some(BinaryImplies l r)
    | BinaryExpr(_, "=", l, r) -> Some(BinaryEq l r)
    | BinaryExpr(_, "!=", l, r) -> Some(BinaryNeq l r)
    | _ -> None
  RewriteBU __Simplify expr

let rec ExtractTopLevelExpressions stmt = 
  match stmt with
  | ExprStmt(e)    -> [e]
  | Assign(e1, e2) -> [e1; e2]
  | Block(slist)   -> slist |> List.fold (fun acc s -> acc @ ExtractTopLevelExpressions s) [] 

let rec PullUpMethodCalls stmt = 
  let stmtList = new System.Collections.Generic.LinkedList<_>()
  let rec __PullUpMethodCalls expr = 
    let newExpr = RewriteBU (fun expr ->  
                               match expr with
                               | MethodOutSelect(_) ->
                                   let vname = SymGen.NewSymFake expr
                                   let e' = VarLiteral(vname)
                                   let var = VarDeclExpr([Var(vname,None,false)], true)
                                   let asgn = BinaryGets var expr
                                   stmtList.AddLast asgn |> ignore
                                   Some(e')
                               | _ -> None
                            ) expr
    newExpr, (stmtList |> List.ofSeq)
  stmtList.Clear()
  match stmt with
  | ExprStmt(e)    -> 
      let e', slist = __PullUpMethodCalls e
      slist @ [ExprStmt(e')]
  | Assign(e1, e2) -> 
      let e2', slist = __PullUpMethodCalls e2
      slist @ [Assign(e1, e2')]
  | Block(slist)   -> slist |> List.fold (fun acc s -> acc @ PullUpMethodCalls s) [] 

//  ==========================================================
/// Very simple for now: 
///   - if "m" is a constructor, everything is modifiable
///   - if the method's post condition contains assignments to fields, everything is modifiable
///   - otherwise, all objects are immutable 
///
/// (TODO: instead it should read the "modifies" clause of a method and figure out what's modifiable from there)
//  ==========================================================
let IsModifiableObj obj (c,m) = 
  let __IsFld name = FindVar c name |> Utils.OptionToBool
  match m with
  | Method(name,_,_,_,_) when name.EndsWith("__mod__") -> true
  | Method(_,_,_,_,true) -> true
  | Method(_,_,_,post,false) -> 
      DescendExpr2 (fun e acc -> 
                      match e with 
                      | BinaryExpr(_,"=",IdLiteral(name),r) when __IsFld name -> true
                      | Dot(_,name) when __IsFld name -> true
                      | _ -> acc
                   ) post false
  | _ -> failwithf "expected a Method but got %O" m