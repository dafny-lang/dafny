module CodeGen

open Ast
open AstUtils
open Utils
open Printer   
open Resolver
open TypeChecker
open DafnyPrinter

let numLoopUnrolls = 2

let rec GetUnrolledFieldValidExpr fldExpr fldName validFunName numUnrolls : Expr = 
  if numUnrolls = 0 then
    TrueLiteral
  else
    BinaryImplies (BinaryNeq fldExpr (IdLiteral("null")))
                  (BinaryAnd (Dot(fldExpr, validFunName))
                             (GetUnrolledFieldValidExpr (Dot(fldExpr, fldName)) fldName validFunName (numUnrolls-1)))

let GetFieldValidExpr fldName validFunName numUnrolls : Expr = 
  GetUnrolledFieldValidExpr (IdLiteral(fldName)) fldName validFunName numUnrolls

let GetFieldsForValidExpr allFields prog : VarDecl list =
  allFields |> List.filter (function Var(name, tp) when IsUserType prog tp -> true
                                     | _                                   -> false)

let GetFieldsValidExprList clsName allFields prog : Expr list =
  let fields = GetFieldsForValidExpr allFields prog
  fields |> List.map (function Var(name, t) -> 
                                 let validFunName, numUnrolls = 
                                   match t with
                                   | Some(ty) when clsName = (GetTypeShortName ty) -> "Valid_self()", numLoopUnrolls
                                   | _ -> "Valid()", 1
                                 GetFieldValidExpr name validFunName numUnrolls
                     )

let PrintValidFunctionCode comp prog : string = 
  let idt = "    "
  let __PrintInvs invs = 
    invs |> List.fold (fun acc e -> List.concat [acc ; SplitIntoConjunts e]) []
         |> PrintSep (" &&" + newline) (fun e -> sprintf "%s(%s)" idt (PrintExpr 0 e))
         |> fun s -> if s = "" then (idt + "true") else s
  let clsName = GetClassName comp
  let vars = GetAllFields comp
  let allInvs = GetInvariantsAsList comp |> DesugarLst
  let fieldsValid = GetFieldsValidExprList clsName vars prog
                                                                
  // TODO: don't hardcode decr vars!!!
//  let decrVars = if List.choose (function Var(n,_) -> Some(n)) vars |> List.exists (fun n -> n = "next") then
//                   ["list"]
//                 else
//                   []
//  (if List.isEmpty decrVars then "" else sprintf "    decreases %s;%s" (PrintSep ", " (fun a -> a) decrVars) newline) +
  "  function Valid_self(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  (__PrintInvs allInvs) + newline +
  "  }" + newline +
  newline +
  "  function Valid(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  "    this.Valid_self() &&" + newline +
  (__PrintInvs fieldsValid) + newline +
  "  }" + newline

let PrintDafnyCodeSkeleton prog methodPrinterFunc: string =
  match prog with
  | Program(components) -> components |> List.fold (fun acc comp -> 
      match comp with  
      | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) as comp ->
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
        (sprintf "%s" (PrintValidFunctionCode comp prog)) + newline +
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
                    | _ -> failwithf "NewObj doesn't have a type: %O" newObjConst
                  ) ""

let PrintObjRefName o (env,ctx) = 
  match Resolve (env,ctx) o with
  | ThisConst(_,_) -> "this";
  | NewObj(name, _) -> PrintGenSym name
  | _ -> failwith ("unresolved object ref: " + o.ToString())

let CheckUnresolved c =
  match c with 
  | Unresolved(_) -> Logger.WarnLine "!!! There are some unresolved constants in the output file !!!"; c 
  | _ -> c

let PrintVarAssignments (heap,env,ctx) indent = 
  let idt = Indent indent
  heap |> Map.fold (fun acc (o,f) l ->
                      let objRef = PrintObjRefName o (env,ctx)
                      let fldName = PrintVarName f
                      let value = TryResolve (env,ctx) l |> CheckUnresolved |> PrintConst
                      acc + (sprintf "%s%s.%s := %s;" idt objRef fldName value) + newline
                   ) ""

let PrintHeapCreationCode (heap,env,ctx) indent = 
  (PrintAllocNewObjects (heap,env,ctx) indent) +
  (PrintVarAssignments (heap,env,ctx) indent)

let GenConstructorCode mthd body =
  let validExpr = IdLiteral("Valid()");
  match mthd with
  | Method(methodName, sign, pre, post, _) -> 
      let __PrintPrePost pfix expr = SplitIntoConjunts expr |> PrintSep newline (fun e -> pfix + (PrintExpr 0 e) + ";")
      let preExpr = pre 
      let postExpr = BinaryAnd validExpr post
      "  method " + methodName + (PrintSig sign) + newline +
      "    modifies this;" + newline +
      (__PrintPrePost "    requires " preExpr) + newline +
      (__PrintPrePost "    ensures " postExpr) + newline +
      "  {" + newline + 
      body + 
      "  }" + newline
  | _ -> ""

// solutions: (comp, constructor) |--> (heap, env, ctx) 
let PrintImplCode prog solutions methodsToPrintFunc =
  let methods = methodsToPrintFunc prog
  PrintDafnyCodeSkeleton prog (fun comp mthd ->
                                 if Utils.ListContains (comp,mthd) methods  then
                                   let mthdBody = match Map.tryFind (comp,mthd) solutions with
                                                  | Some(heap,env,ctx) -> PrintHeapCreationCode (heap,env,ctx) 4
                                                  | _ -> "    //unable to synthesize" + newline
                                   (GenConstructorCode mthd mthdBody) + newline
                                 else
                                   ""
                              )