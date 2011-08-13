//  ####################################################################
///   Utility functions for manipulating AST elements
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module AstUtils

open Ast
open Logger
open Utils

let ThisLiteral = ObjLiteral("this")
let NullLiteral = ObjLiteral("null")

let rec Rewrite rewriterFunc expr =
  let __RewriteOrRecurse e =
    match rewriterFunc e with
    | Some(ee) -> ee
    | None -> Rewrite rewriterFunc e 
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
  | Dot(e, id)                       -> Dot(__RewriteOrRecurse e, id)
  | ForallExpr(vars,e)               -> ForallExpr(vars, __RewriteOrRecurse e)   
  | UnaryExpr(op,e)                  -> UnaryExpr(op, __RewriteOrRecurse e)
  | LCIntervalExpr(e)                -> LCIntervalExpr(__RewriteOrRecurse e)
  | SeqLength(e)                     -> SeqLength(__RewriteOrRecurse e)
  | SelectExpr(e1, e2)               -> SelectExpr(__RewriteOrRecurse e1, __RewriteOrRecurse e2)
  | BinaryExpr(p,op,e1,e2)           -> BinaryExpr(p, op, __RewriteOrRecurse e1, __RewriteOrRecurse e2)
  | IteExpr(e1,e2,e3)                -> IteExpr(__RewriteOrRecurse e1, __RewriteOrRecurse e2, __RewriteOrRecurse e3) 
  | UpdateExpr(e1,e2,e3)             -> UpdateExpr(__RewriteOrRecurse e1, __RewriteOrRecurse e2, __RewriteOrRecurse e3) 
  | SequenceExpr(exs)                -> SequenceExpr(exs |> List.map __RewriteOrRecurse)
  | SetExpr(exs)                     -> SetExpr(exs |> List.map __RewriteOrRecurse)
  | MethodCall(rcv,cname,mname,ins)  -> MethodCall(__RewriteOrRecurse rcv, cname, mname, ins |> List.map __RewriteOrRecurse)

//  ====================================================
/// Substitutes all occurences of all IdLiterals having 
/// the same name as one of the variables in "vars" with
/// VarLiterals, in "expr".
//  ====================================================
let RewriteVars vars expr = 
  let __IdIsArg id = vars |> List.exists (function Var(name,_) -> name = id)
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
    | "<"  -> Some(">")
    | ">"  -> Some("<")
    | ">=" -> Some("<=")
    | "<=" -> Some(">=")
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
  | Dot(e, _)
  | ForallExpr(_,e)
  | LCIntervalExpr(e)
  | UnaryExpr(_,e)           
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
  | Dot(e, _)
  | ForallExpr(_,e)
  | LCIntervalExpr(e)
  | UnaryExpr(_,e)           
  | SeqLength(e)                     -> __Pipe (e :: [])
  | SelectExpr(e1, e2)
  | BinaryExpr(_,_,e1,e2)            -> __Pipe (e1 :: e2 :: [])
  | IteExpr(e1,e2,e3)
  | UpdateExpr(e1,e2,e3)             -> __Pipe (e1 :: e2 :: e3 :: [])
  | MethodCall(rcv,_,_,aparams)      -> __Pipe (rcv :: aparams)
  | SequenceExpr(exs)                
  | SetExpr(exs)                     -> __Pipe exs

let PrintGenSym name =
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
  | _ -> UnaryExpr("!", sub)

//  =======================================================================
/// Returns a binary PLUS of the two given expressions
//  =======================================================================
let BinaryPlus (lhs: Expr) (rhs: Expr) = 
  BinaryExpr(50, "+", lhs, rhs)

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
  | BoolLiteral(false), _ -> FalseLiteral
  | BoolLiteral(true), _  -> rhs
  | _, BoolLiteral(true)  -> lhs
  | _, BoolLiteral(false) -> UnaryNot(lhs)
  | _ -> BinaryExpr(20, "==>", lhs, rhs)

//  =======================================================
/// Constructors for binary EQ/NEQ of two given expressions
//  =======================================================
let BinaryNeq lhs rhs = BinaryExpr(40, "!=", lhs, rhs)
let BinaryEq lhs rhs = BinaryExpr(40, "=", lhs, rhs)

//  =======================================================
/// Constructor for binary GETS
//  =======================================================
let BinaryGets lhs rhs = Assign(lhs, rhs)

//  =======================================================
/// Constructors for binary IN/!IN of two given expressions
//  =======================================================
let BinaryIn lhs rhs = BinaryExpr(40, "in", lhs, rhs)
let BinaryNotIn lhs rhs = BinaryExpr(40, "!in", lhs, rhs)
  
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
  | ObjLiteral("this") -> ThisConst("this",None)
  | ObjLiteral("null") -> NullConst
  | ObjLiteral(name) -> Unresolved(name)
  | IdLiteral(id) -> Unresolved(id)
  | VarLiteral(id) -> VarConst(id)
  | SequenceExpr(elist) -> SeqConst(elist |> List.map Expr2Const)
  | SetExpr(elist) -> SetConst(elist |> List.map Expr2Const |> Set.ofList)
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

let GetAbstractFields comp = 
  match comp with 
  | Component(Class(_,_,members), _, _) -> FilterFieldMembers members
  | _ -> failwithf "internal error: invalid component: %O" comp
    
let GetConcreteFields comp = 
  match comp with 
  | Component(_, Model(_,_,cVars,_,_), _) -> cVars
  | _ -> failwithf "internal error: invalid component: %O" comp
     
//  =================================
/// Returns all fields of a component
//  =================================
let GetAllFields comp = 
  List.concat [GetAbstractFields comp; GetConcreteFields comp]
    
//  ===========================================================
/// Returns a map (Type |--> Set<Var>) where all 
/// the given fields are grouped by their type
///
/// ensures: forall v :: v in ret.values.elems ==> v in fields
/// ensures: forall k :: k in ret.keys ==> 
///            forall v1, v2 :: v1, v2 in ret[k].elems ==> 
///              v1.type = v2.type
//  ===========================================================
let rec GroupFieldsByType fields = 
  match fields with
  | Var(name, ty) :: rest -> 
      let map = GroupFieldsByType rest
      let fldSet = Map.tryFind ty map |> Utils.ExtractOptionOr Set.empty
      map |> Map.add ty (fldSet |> Set.add (Var(name, ty)))
  | [] -> Map.empty
                    
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

let GetMethodInArgs mthd = 
  match mthd with
  | Method(_,Sig(ins, _),_,_,_) -> ins
  | _ -> failwith ("not a method: " + mthd.ToString())

let GetMethodOutArgs mthd = 
  match mthd with
  | Method(_,Sig(_, outs),_,_,_) -> outs
  | _ -> failwith ("not a method: " + mthd.ToString())

let GetMethodArgs mthd = 
  let ins = GetMethodInArgs mthd
  let outs = GetMethodOutArgs mthd
  List.concat [ins; outs]

let IsConstructor mthd = 
  match mthd with
  | Method(_,_,_,_,isConstr) -> isConstr
  | _ -> failwithf "expected a method but got %O" mthd

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
/// Returns component name
//  ==================================
let GetComponentName comp = 
  match comp with
  | Component(Class(name,_,_),_,_) -> name
  | _ -> failwithf "invalid component %O" comp

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
//let FindCompVar prog clsName fldName =
//  let copt = FindComponent prog clsName
//  match copt with
//  | Some(comp) -> 
//      GetAllFields comp |> List.filter (function Var(name,_) when name = fldName -> true | _ -> false)
//                        |> Utils.ListToOption
//  | None -> None

let FindVar comp fldName =
  GetAllFields comp |> List.filter (function Var(name,_) when name = fldName -> true | _ -> false)
                    |> Utils.ListToOption

//  ======================================
/// Returns the frame of a given component
//  ======================================
let GetFrame comp = 
  match comp with 
  | Component(_, Model(_,_,_,frame,_), _) -> frame
  | _ -> failwithf "not a valid component %O" comp

let GetFrameFields comp =
  let frame = GetFrame comp
  frame |> List.choose (function IdLiteral(name) -> Some(name) | _ -> None) // TODO: is it really enough to handle only IdLiteral's
        |> List.choose (fun varName -> 
                          let v = FindVar comp varName
                          Utils.ExtractOptionMsg ("field not found: " + varName) v |> ignore
                          v
                       )

//  ==============================================
/// Checks whether two given methods are the same.
///
/// Methods are the same if their names are the 
/// same and their components have the same name.
//  ==============================================
let CheckSameMethods (c1,m1) (c2,m2) = 
  GetComponentName c1 = GetComponentName c2 && GetMethodName m1 = GetMethodName m2

////////////////////////

let AddReplaceMethod prog comp newMthd oldMethod =
  match prog, comp with
  | Program(clist), Component(Class(cname, ctypeParams, members), model, code) ->
      let newMembers = 
        match oldMethod with
        | None -> members @ [newMthd]
        | Some(m) -> Utils.ListReplace m newMthd members
      let newCls = Class(cname, ctypeParams, newMembers)
      let newComp = Component(newCls, model, code)
      let newProg = Program(Utils.ListReplace comp newComp clist)
      newProg, newComp
  | _ -> failwithf "Invalid component: %O" comp

let AddPrecondition prog comp m e =
  match m with
  | Method(mn, sgn, pre, post, cstr) ->
      let newMthd = Method(mn, sgn, BinaryAnd pre e, post, cstr)
      let newProg, newComp = AddReplaceMethod prog comp newMthd (Some(m))
      newProg, newComp, newMthd
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

let rec __EvalSym resolverFunc ctx expr = 
  match expr with
  | IntLiteral(_)  -> expr
  | BoolLiteral(_) -> expr
  | BoxLiteral(_)  -> expr
  | ObjLiteral(_)  -> expr
  | Star           -> expr //TODO: can we do better?
  | VarDeclExpr(_) -> expr
  | VarLiteral(id) -> 
      try 
        let _,e = ctx |> List.find (fun (v,e) -> GetVarName v = id)
        e
      with 
      | ex -> resolverFunc expr None
  | IdLiteral(_)   -> resolverFunc expr None
  | Dot(e, str)    -> 
      let discr = __EvalSym resolverFunc ctx e
      resolverFunc discr (Some(str))
  | SeqLength(e)   -> 
      let e' = __EvalSym resolverFunc ctx e
      match e' with
      | SequenceExpr(elist) -> IntLiteral(List.length elist)
      | _ -> SeqLength(e')
  | SequenceExpr(elist) -> 
      let elist' = elist |> List.fold (fun acc e -> __EvalSym resolverFunc ctx e :: acc) [] |> List.rev
      SequenceExpr(elist')
  | SetExpr(elist) -> 
      let eset' = elist |> List.fold (fun acc e -> Set.add (__EvalSym resolverFunc ctx e) acc) Set.empty
      SetExpr(Set.toList eset')
  | MethodCall(rcv,cname, mname,aparams) ->
      let rcv' = __EvalSym resolverFunc ctx rcv
      let aparams' = aparams |> List.fold (fun acc e -> __EvalSym resolverFunc ctx e :: acc) [] |> List.rev
      MethodCall(rcv', cname, mname, aparams')
  | LCIntervalExpr(_) -> expr
  | SelectExpr(lst, idx) ->
      let lst' = __EvalSym resolverFunc ctx lst
      let idx' = __EvalSym resolverFunc ctx idx 
      match lst', idx' with
      | SequenceExpr(elist), IntLiteral(n) -> elist.[n] 
      | SequenceExpr(elist), LCIntervalExpr(startIdx) ->
          let startIdx' = __EvalSym resolverFunc ctx startIdx
          match startIdx' with
          | IntLiteral(startIdxInt) -> 
              let rec __Skip n l = if n = 0 then l else __Skip (n-1) (List.tail l)
              SequenceExpr(__Skip startIdxInt elist)
          | _ -> SelectExpr(lst', idx')
      | _ -> SelectExpr(lst', idx')
  | UpdateExpr(lst,idx,v) ->
      let lst', idx', v' = __EvalSym resolverFunc ctx lst, __EvalSym resolverFunc ctx idx, __EvalSym resolverFunc ctx v
      match lst', idx', v' with
      | SequenceExpr(elist), IntLiteral(n), _ -> SequenceExpr(Utils.ListSet n v' elist)
      | _ -> UpdateExpr(lst', idx', v')
  | IteExpr(c, e1, e2) ->
      let c' = __EvalSym resolverFunc ctx c
      match c' with
      | BoolLiteral(b) -> if b then __EvalSym resolverFunc ctx e1 else __EvalSym resolverFunc ctx e2
      | _ -> IteExpr(c', __EvalSym resolverFunc ctx e1, __EvalSym resolverFunc ctx e2)
  | BinaryExpr(p,op,e1,e2) ->
      let e1' = lazy (__EvalSym resolverFunc ctx e1)
      let e2' = lazy (__EvalSym resolverFunc ctx e2)
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
          | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) < (List.length s2))
          | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) < (List.length s2))
          | _ -> recomposed.Force()
      | "<=" -> 
          let e1'' = e1'.Force()
          let e2'' = e2'.Force()
          let eq = __CheckEqual e1'' e2''
          match eq with
          | Some(true) -> TrueLiteral
          | _ -> match e1'', e2'' with
                 | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 <= n2)
                 | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) <= (List.length s2))
                 | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) <= (List.length s2))
                 | _ -> recomposed.Force()
      | ">" -> 
          match e1'.Force(), e2'.Force() with
          | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 > n2)
          | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) > (List.length s2))
          | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) > (List.length s2))
          | _ -> recomposed.Force()
      | ">=" -> 
          let e1'' = e1'.Force()
          let e2'' = e2'.Force()
          let eq = __CheckEqual e1'' e2''
          match eq with
          | Some(true) -> TrueLiteral
          | _ -> match e1'', e2'' with
                 | IntLiteral(n1), IntLiteral(n2)     -> BoolLiteral(n1 >= n2)
                 | SetExpr(s1), SetExpr(s2)           -> BoolLiteral((List.length s1) >= (List.length s2))
                 | SequenceExpr(s1), SequenceExpr(s2) -> BoolLiteral((List.length s1) >= (List.length s2))
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
          | _, SequenceExpr(s)  -> BoolLiteral(Utils.ListContains (e1'.Force()) s)
          | _ -> recomposed.Force()
      | "!in" -> 
          match e1'.Force(), e2'.Force() with
          | _, SetExpr(s)       
          | _, SequenceExpr(s)  -> BoolLiteral(not (Utils.ListContains (e1'.Force()) s))
          | _ -> recomposed.Force()
      | "+" -> 
          let e1'' = e1'.Force();
          let e2'' = e2'.Force();
          match e1'', e2'' with
          | IntLiteral(n1), IntLiteral(n2) -> IntLiteral(n1 + n2)
          | SequenceExpr(l1), SequenceExpr(l2) -> SequenceExpr(List.append l1 l2)
          | SetExpr(s1), SetExpr(s2) -> SetExpr(Set.union (Set.ofList s1) (Set.ofList s2) |> Set.toList)
          | SetExpr(s), _ -> SetExpr(Set.add e2'' (Set.ofList s) |> Set.toList)
          | _, SetExpr(s) -> SetExpr(Set.add e1'' (Set.ofList s) |> Set.toList)
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
              | BoolLiteral(false), _            -> BoolLiteral(false)
              | _, BoolLiteral(false)            -> BoolLiteral(false)
              | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 && b2)
              | _ -> BinaryAnd (e1'.Force()) (e2'.Force())
      | "||" -> 
          // shortcircuit
          match e1'.Force() with
          | BoolLiteral(true) -> BoolLiteral(true)
          | _ ->
              match e1'.Force(), e2'.Force() with
              | BoolLiteral(true), _             -> BoolLiteral(true)
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
              match e1'', e2'' with
              | BoolLiteral(false), _            -> BoolLiteral(true)
              | _, BoolLiteral(true)             -> BoolLiteral(true)
              | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral((not b1) || b2)
              | _ -> BinaryImplies (e1'.Force()) (e2'.Force())
      | "<==>" -> 
          match e1'.Force(), e2'.Force() with
          | BoolLiteral(b1), BoolLiteral(b2) -> BoolLiteral(b1 = b2)
          | x, BoolLiteral(b)
          | BoolLiteral(b), x -> if b then x else UnaryNot(x)
          | _ -> recomposed.Force()
      | _ -> recomposed.Force()
  | UnaryExpr(op, e) ->
      let e' = __EvalSym resolverFunc ctx e
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
            let e' = __EvalSym resolverFunc ctx' (ForallExpr(restV, e))
            let erest = __ExhaustVar v restV restD
            (* __EvalSym resolverFunc ctx' *) 
            BinaryAnd e' erest
        | [] -> BoolLiteral(true)
      let rec __TraverseVars vars =
        match vars with
        | v :: restV -> 
            try 
              let vDom = GetVarDomain resolverFunc ctx v e
              __ExhaustVar v restV vDom
            with
              | ex -> ForallExpr([v], __TraverseVars restV) 
        | [] -> __EvalSym resolverFunc ctx e
      (* --- function body starts here --- *)
      __TraverseVars vars
and GetVarDomain resolverFunc ctx var expr = 
  match expr with 
  | BinaryExpr(_, "==>", lhs, rhs) -> 
      let conjs = SplitIntoConjunts lhs
      conjs |> List.fold (fun acc e ->
                            match e with
                            | BinaryExpr(_, "in", VarLiteral(vn), rhs) when GetVarName var = vn ->
                                match __EvalSym resolverFunc ctx rhs with
                                | SetExpr(elist)
                                | SequenceExpr(elist) -> elist |> List.append acc
                                | _ -> raise DomainNotInferred
                            | BinaryExpr(_, op, VarLiteral(vn),oth)
                            | BinaryExpr(_, op, oth, VarLiteral(vn)) when GetVarName var = vn && Set.ofList ["<"; "<="; ">"; ">="] |> Set.contains op -> 
                                failwith "Not implemented yet"
                            | _ -> raise DomainNotInferred) []
  | _ -> 
      Logger.WarnLine ("unknown pattern for a quantified expression; cannot infer domain of quantified variable \"" + (GetVarName var) + "\"")
      raise DomainNotInferred

let EvalSym resolverFunc expr = 
  __EvalSym resolverFunc [] expr 
  
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
    | SequenceExpr(_)        -> expr 
    // forall v :: v in {a1 a2 ... an} ==> e  ~~~> e[v/a1] && e[v/a2] && ... && e[v/an] 
    // forall v :: v in [a1 a2 ... an] ==> e  ~~~> e[v/a1] && e[v/a2] && ... && e[v/an] 
    | ForallExpr([Var(vn1,ty1)] as v, (BinaryExpr(_, "==>", BinaryExpr(_, "in", VarLiteral(vn2), rhsCol), sub) as ee)) when vn1 = vn2 ->
        match rhsCol with 
        | SetExpr(elist)
        | SequenceExpr(elist) -> elist |> List.fold (fun acc e -> BinaryAnd acc (__Desugar (Substitute (VarLiteral(vn2)) e sub))) TrueLiteral
        | _ -> ForallExpr(v, __Desugar ee)
    | ForallExpr(v,e)        -> ForallExpr(v, __Desugar e)
    | LCIntervalExpr(e)      -> LCIntervalExpr(__Desugar e)
    | UnaryExpr(op,e)        -> UnaryExpr(op, __Desugar e)
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
    | ForallExpr(vars,e)                   -> let newLocals = vars |> List.map (function Var(name,_) -> name) |> Set.ofList |> Set.union locals
                                              ForallExpr(vars, __ChangeThis newLocals e)   
    | LCIntervalExpr(e)                    -> LCIntervalExpr(__ChangeThis locals e)
    | UnaryExpr(op,e)                      -> UnaryExpr(op, __ChangeThis locals e)
    | SeqLength(e)                         -> SeqLength(__ChangeThis locals e)
    | SelectExpr(e1, e2)                   -> SelectExpr(__ChangeThis locals e1, __ChangeThis locals e2)
    | BinaryExpr(p,op,e1,e2)               -> BinaryExpr(p, op, __ChangeThis locals e1, __ChangeThis locals e2)
    | IteExpr(e1,e2,e3)                    -> IteExpr(__ChangeThis locals e1, __ChangeThis locals e2, __ChangeThis locals e3) 
    | UpdateExpr(e1,e2,e3)                 -> UpdateExpr(__ChangeThis locals e1, __ChangeThis locals e2, __ChangeThis locals e3) 
    | SequenceExpr(exs)                    -> SequenceExpr(exs |> List.map (__ChangeThis locals))
    | SetExpr(exs)                         -> SetExpr(exs |> List.map (__ChangeThis locals))
    | MethodCall(rcv,cname, mname,aparams) -> MethodCall(__ChangeThis locals rcv, cname, mname, aparams |> List.map (__ChangeThis locals))
  (* --- function body starts here --- *)
  __ChangeThis Set.empty expr

let rec ExtractTopLevelExpressions stmt = 
  match stmt with
  | ExprStmt(e)    -> [e]
  | Assign(e1, e2) -> [e1; e2]
  | Block(slist)   -> slist |> List.fold (fun acc s -> acc @ ExtractTopLevelExpressions s) [] 

//  ==========================================================
/// Very simple for now: 
///   - if "m" is a constructor, everything is modifiable
///   - otherwise, all objects are immutable (TODO: instead it should read the "modifies" clause of a method and figure out what's modifiable from there)
//  ==========================================================
let IsModifiableObj obj m = 
  match m with
  | Method(_,_,_,_,isConstr) -> isConstr
  | _ -> failwithf "expected a Method but got %O" m