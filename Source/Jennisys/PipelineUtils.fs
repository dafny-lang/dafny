//  ####################################################################
///   Utility functions for executing shell commands and 
///   running Dafny in particular
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module PipelineUtils
  
open Logger

let dafnyScratchSuffix = "scratch"
let dafnyVerifySuffix = "verify"
let dafnyUnifSuffix = "unif"
let dafnySynthFileNameTemplate = @"c:\tmp\jennisys-synth_###.dfy"
let dafnyModularSynthFileNameTemplate = @"c:\tmp\jennisys-synth_###_mod.dfy"

let mutable lastDafnyExitCode = 0 //TODO: how to avoid this muttable state?

let CreateEmptyModelFile modelFile = 
  use mfile = System.IO.File.CreateText(modelFile)
  fprintf mfile ""

//  =======================================================
/// Runs Dafny on the given "inputFile" and prints 
/// the resulting model to the given "modelFile"
//  =======================================================
let RunDafny inputFile modelFile =
  //TraceLine "\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ Running Dafny @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
  CreateEmptyModelFile modelFile
  async {
    use proc = new System.Diagnostics.Process()
    proc.StartInfo.FileName  <- @"c:\tmp\StartDafny-jen.bat"
    proc.StartInfo.Arguments <- (sprintf "/mv:%s /timeLimit:%d %s" modelFile Options.CONFIG.timeout inputFile)
    proc.StartInfo.WindowStyle <- System.Diagnostics.ProcessWindowStyle.Hidden
    assert proc.Start()
    proc.WaitForExit() 
    lastDafnyExitCode <- proc.ExitCode
  } |> Async.RunSynchronously
  
//  =======================================================
/// Runs Dafny on the given "dafnyCode" and returns models
//  =======================================================
let RunDafnyProgram dafnyProgram suffix =
  let inFileName = @"c:\tmp\jennisys-" + suffix + ".dfy" 
  let modelFileName = @"c:\tmp\jennisys-" + suffix + ".bvd" 
  use file = System.IO.File.CreateText(inFileName)
  file.AutoFlush <- true  
  fprintfn file "%s" dafnyProgram
  file.Close()
  // run Dafny
  RunDafny inFileName modelFileName
  // read models from the model file
  use modelFile = System.IO.File.OpenText(modelFileName)
  Microsoft.Boogie.Model.ParseModels modelFile

//  =======================================================
/// Checks whether the given dafny program verifies
//  =======================================================  
let CheckDafnyProgram dafnyProgram suffix =
  let models = RunDafnyProgram dafnyProgram suffix
  // if there are no models, verification was successful
  lastDafnyExitCode = 0 && models.Count = 0       
