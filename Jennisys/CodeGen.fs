module CodeGen

open Ast
open AstUtils
open Utils
open Printer   
open TypeChecker
open DafnyPrinter

let GetFieldValidExpr (name: string) : Expr = 
  BinaryImplies (BinaryNeq (IdLiteral(name)) (IdLiteral("null"))) (Dot(IdLiteral(name), "Valid()"))

let GetFieldsForValidExpr (allFields: VarDecl list) prog : VarDecl list =
  allFields |> List.filter (function Var(name, tp) when IsUserType prog tp -> true
                                     | _                                   -> false)

let GetFieldsValidExprList (allFields: VarDecl list) prog : Expr list =
  let fields = GetFieldsForValidExpr allFields prog
  fields |> List.map (function Var(name, _) -> GetFieldValidExpr name)

let PrintValidFunctionCode clsMembers modelInv vars prog : string = 
  let invMembers = clsMembers |> List.filter (function Invariant(_) -> true | _ -> false)
  let clsInvs = invMembers |> List.choose (function Invariant(exprList) -> Some(exprList) | _ -> None) |> List.concat
  let allInvs = modelInv :: clsInvs
  let fieldsValid = GetFieldsValidExprList vars prog
  let idt = "    "
  let invsStr = List.concat [allInvs ; fieldsValid] |> List.fold (fun acc e -> List.concat [acc ; SplitIntoConjunts e]) []
                                                    |> List.fold (fun acc (e: Expr) -> 
                                                                    if acc = "" then
                                                                      sprintf "%s(%s)" idt (PrintExpr 0 e)
                                                                    else
                                                                      acc + " &&" + newline + sprintf "%s(%s)" idt (PrintExpr 0 e)) ""
  // TODO: don't hardcode decr vars!!!
  let decrVars = if List.choose (function Var(n,_) -> Some(n)) vars |> List.exists (fun n -> n = "next") then
                   ["list"]
                 else
                   []
  "  function Valid(): bool" + newline +
  "    reads *;" + newline +
  (if List.isEmpty decrVars then "" else sprintf "    decreases %s;%s" (PrintSep ", " (fun a -> a) decrVars) newline) +
  "  {" + newline + 
  invsStr + newline +
  "  }" + newline

let PrintDafnyCodeSkeleton prog methodPrinterFunc: string =
  match prog with
  | Program(components) -> components |> List.fold (fun acc comp -> 
      match comp with  
      | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) ->
        let aVars = FilterFieldMembers members
        let allVars = List.concat [aVars ; cVars];
        let compMethods = FilterConstructorMembers members
        // Now print it as a Dafny program
        acc + 
        (sprintf "class %s%s {" name (PrintTypeParams typeParams)) + newline +       
        // the fields: original abstract fields plus concrete fields
        (sprintf "%s" (PrintFields aVars 2 true)) + newline +     
        (sprintf "%s" (PrintFields cVars 2 false)) + newline +                           
        // generate the Valid function
        (sprintf "%s" (PrintValidFunctionCode members inv allVars prog)) + newline +
        // call the method printer function on all methods of this component
        (compMethods |> List.fold (fun acc m -> acc + (methodPrinterFunc comp m)) "") +
        // the end of the class
        "}" + newline + newline
      | _ -> assert false; "") ""
  
let PrintAllocNewObjects (heap,env,ctx) indent = 
  let idt = Indent indent
  env |> Map.fold (fun acc l v ->
                     match v with 
                     | NewObj(_,_) -> acc |> Set.add v
                     | _ -> acc
                  ) Set.empty
      |> Set.fold (fun acc newObjConst ->
                    match newObjConst with
                    | NewObj(name, Some(tp)) -> acc + (sprintf "%svar %s := new %s;%s" idt (PrintGenSym name) (PrintType tp) newline)
                    | _ -> failwith ("NewObj doesn't have a type: " + newObjConst.ToString())
                  ) ""

let PrintObjRefName o (env,ctx) = 
  match Resolve o (env,ctx) with
  | ThisConst(_,_) -> "this";
  | NewObj(name, _) -> PrintGenSym name
  | _ -> failwith ("unresolved object ref: " + o.ToString())

let PrintVarAssignments (heap,env,ctx) indent = 
  let idt = Indent indent
  heap |> Map.fold (fun acc (o,f) l ->
                      let objRef = PrintObjRefName o (env,ctx)
                      let fldName = PrintVarName f
                      let value = Resolve l (env,ctx) |> PrintConst
                      acc + (sprintf "%s%s.%s := %s;" idt objRef fldName value) + newline
                   ) ""

let PrintHeapCreationCode (heap,env,ctx) indent = 
  (PrintAllocNewObjects (heap,env,ctx) indent) +
  (PrintVarAssignments (heap,env,ctx) indent)

let GenConstructorCode mthd body =
  match mthd with
  | Constructor(methodName, sign, pre, post) -> 
      "  method " + methodName + (PrintSig sign) + newline +
      "    modifies this;" + newline +
      "    requires " + (PrintExpr 0 pre) + ";" + newline +
      "    ensures " + (PrintExpr 0 post) + ";" + newline + 
      "    ensures Valid(); " + newline +
      "  {" + newline + 
      body + 
      "  }" + newline
  | _ -> ""

// solutions: (comp, constructor) |--> (heap, env, ctx) 
let PrintImplCode prog solutions =
  PrintDafnyCodeSkeleton prog (fun comp mthd ->
                                 let mthdBody = match Map.tryFind (comp,mthd) solutions with
                                                | Some(heap,env,ctx) -> PrintHeapCreationCode (heap,env,ctx) 4
                                                | _ -> "    //unable to synthesize" + newline
                                 (GenConstructorCode mthd mthdBody) + newline
                              )