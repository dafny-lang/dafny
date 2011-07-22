//  ####################################################################
///   This module is intended to store and handle configuration options
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module Options

open Utils

type Config = {
   help: bool;
   inputFilename: string;
   methodToSynth: string;
   verifyPartialSolutions: bool;
   verifySolutions: bool;
   checkUnifications: bool;
   genRepr: bool;
   timeout: int;
   numLoopUnrolls: int;
}

type CfgOption<'a> = {
   optionName: string; 
   optionType: string;
   optionSetter: 'a -> Config -> Config;
   descr: string;
}

exception InvalidCmdLineArg of string
exception InvalidCmdLineOption of string

let CheckNonEmpty value optName =
  if value = "" then raise (InvalidCmdLineArg("A value for option " + optName + " must not be empty")) else value

let CheckInt value optName =
  try 
    System.Int32.Parse value
  with 
    | ex -> raise (InvalidCmdLineArg("A value for option " + optName + " must be a boolean"))

let CheckBool value optName =
  if value = "" then
    true
  else
    try 
      System.Boolean.Parse value
    with 
      | ex -> raise (InvalidCmdLineArg("A value for option " + optName + " must be an integer"))

let cfgOptions = [
  { optionName = "help";            optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with help                   =      CheckBool v "help"});           descr = "description not available"; }
  { optionName = "method";          optionType = "string"; optionSetter = (fun v (cfg: Config) -> {cfg with methodToSynth          = CheckNonEmpty v "method"});          descr = "description not available"; }
  { optionName = "verifyParSol";    optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifyPartialSolutions =      CheckBool v "verifyParSol"});   descr = "description not available"; }
  { optionName = "noVerifyParSol";  optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifyPartialSolutions = not (CheckBool v "verifyParSol")});  descr = "description not available"; }
  { optionName = "verifySol";       optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifySolutions        =      CheckBool v "verifySol"});      descr = "description not available"; }
  { optionName = "noVerifySol";     optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with verifySolutions        = not (CheckBool v "verifySol")});     descr = "description not available"; } 
  { optionName = "checkUnifs";      optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with checkUnifications      =      CheckBool v "checkUnifs"});     descr = "description not available"; } 
  { optionName = "noCheckUnifs";    optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with checkUnifications      = not (CheckBool v "noCheckUnifs")});  descr = "description not available"; }
  { optionName = "genRepr";         optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with genRepr                =      CheckBool v "genRepr"});        descr = "description not available"; }
  { optionName = "noGenRepr";       optionType = "bool";   optionSetter = (fun v (cfg: Config) -> {cfg with genRepr                = not (CheckBool v "noGenRepr")});     descr = "description not available"; }
  { optionName = "timeout";         optionType = "int";    optionSetter = (fun v (cfg: Config) -> {cfg with timeout                =      CheckInt v "timeout"});         descr = "description not available"; }
  { optionName = "unrolls";         optionType = "int";    optionSetter = (fun v (cfg: Config) -> {cfg with numLoopUnrolls         =      CheckInt v "unrolls"});         descr = "description not available"; }
]

let cfgOptMap = cfgOptions |> List.fold (fun acc o -> acc |> Map.add o.optionName o) Map.empty

let newline = System.Environment.NewLine

let PrintHelpMsg = 
  let maxw = cfgOptions |> List.fold (fun acc o -> if String.length o.optionName > acc then String.length o.optionName else acc) 0
  let maxwStr = sprintf "%d" (maxw + 2)
  let strf = new Printf.StringFormat<_>("  %-" + maxwStr + "s: %-6s | %s")
  let rec __PrintHelp optLst = 
    match optLst with
    | fs :: []   -> (sprintf strf fs.optionName fs.optionType fs.descr)
    | fs :: rest -> (sprintf strf fs.optionName fs.optionType fs.descr) + newline + (__PrintHelp rest)
    | [] -> ""
  (* --- function body starts here --- *)
  newline +
  "Jennisys usage: Jennisys [ option ... ] filename" + newline +
  "  where <option> is one of " + newline + newline +
  "  ----- General options -----------------------------------------------------" + newline + 
  "        (available switches are: /, -, --)" + newline + newline +
  (__PrintHelp cfgOptions)

let defaultConfig: Config = {
  help              = false;
  inputFilename     = "";
  methodToSynth     = "*";
  verifyPartialSolutions = true;
  verifySolutions   = true;
  checkUnifications = false;
  genRepr           = false;
  timeout           = 0;
  numLoopUnrolls    = 2;
}

/// Should not be mutated outside the ParseCmdLineArgs method, which is 
/// typically called only once at the beginning of the program execution 
let mutable CONFIG = defaultConfig

let ParseCmdLineArgs args = 
  let __StripSwitches str =
    match str with 
    | Prefix "--" x 
    | Prefix "-" x
    | Prefix "/" x -> x
    | _ -> str

  let __Split (str: string) =
    let stripped = __StripSwitches str
    if stripped = str then
      ("",str) 
    else
      let splits = stripped.Split([| ':' |])
      if splits.Length > 2 then raise (InvalidCmdLineOption("more than 2 colons in " + str))
      if splits.Length = 2 then
        let opt = splits.[0]
        let value = splits.[1]
        (opt,value)
      else
        let x = __StripSwitches splits.[0]
        (x, "")
                 
  let rec __Parse args cfg =
    match args with
    | fs :: rest -> 
        let opt,value = __Split fs
        if opt = "" then
          __Parse rest { cfg with inputFilename = CheckNonEmpty value opt }
        else 
          match Map.tryFind opt cfgOptMap with
          | Some(opt) -> __Parse rest (opt.optionSetter value cfg)
          | None -> raise (InvalidCmdLineOption("Unknown option: " + opt))
    | [] -> cfg   
    
  (* --- function body starts here --- *)           
  CONFIG <- __Parse args defaultConfig

