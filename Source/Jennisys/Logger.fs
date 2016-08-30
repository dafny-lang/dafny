//  #######################################################
///   Simple logging facility
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  #######################################################

module Logger
             
let newline =  System.Environment.NewLine

let _ALL = 100
let _TRACE = 90
let _DEBUG = 70
let _INFO = 50
let _WARN = 40
let _ERROR = 20
let _NONE = 0

let logLevel = _ALL

let Log level msg =
  if logLevel >= level then
    printf "%s" msg

let LogLine level msg = 
  Log level (msg + newline)

let Trace msg = Log _TRACE msg
let TraceLine msg = LogLine _TRACE msg

let Debug msg = Log _DEBUG msg
let DebugLine msg = LogLine _DEBUG msg

let Info msg = Log _INFO msg
let InfoLine msg = LogLine _INFO msg

let Warn msg = Log _WARN msg
let WarnLine msg = LogLine _WARN msg

let Error msg = Log _ERROR msg
let ErrorLine msg = LogLine _ERROR msg