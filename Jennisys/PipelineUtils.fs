/// Utility functions for executing shell commands and 
/// running Dafny in particular
///
/// author: Aleksandar Milicevic (t-alekm@microsoft.com)

module PipelineUtils
  
let dafnyScratchFile = @"c:\tmp\jennisys-scratch.dfy"
let dafnyVerifyFile = @"c:\tmp\jennisys-verify.dfy"
let dafnyModelFile = @"c:\tmp\jennisys-scratch.bvd"
let dafnyVerifyModelFile = @"c:\tmp\jennisys-verify.bvd"
let dafnyOutFile = @"c:\tmp\jennisys-scratch.out"
let dafnySynthFile = @"c:\tmp\jennisys-synth.dfy"

let CreateEmptyModelFile modelFile = 
  use mfile = System.IO.File.CreateText(modelFile)
  fprintf mfile ""

let RunDafny inputFile modelFile =
  CreateEmptyModelFile modelFile
  async {
    use proc = new System.Diagnostics.Process()
    proc.StartInfo.FileName  <- @"c:\tmp\StartDafny-jen.bat"
    proc.StartInfo.Arguments <- "/mv:" + modelFile + " " + inputFile
    assert proc.Start()
    proc.WaitForExit() 
  } |> Async.RunSynchronously     
