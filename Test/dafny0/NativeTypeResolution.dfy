// RUN: %exits-with 2 %dafny /printTooltips /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype V = x | 0 <= x < 200  // byte
newtype {:nativeType "byte"} W = x | -2 <= x < 2  // error: cannot be byte
newtype {:nativeType "int","byte"} X = x | -2 <= x < 2  // error: cannot be byte
newtype {:nativeType "byte"} Y = x | 0 <= x < 2  // byte (but no tool tip)
newtype {:nativeType "int","byte","long"} Z = x | -2 <= x < 2  // error: cannot be byte

newtype {:nativeType "number","int","int","byte"} A = x | 0 <= x < 256  // int
newtype {:nativeType "byte","number","int","int"} B = x | 0 <= x < 256  // byte
newtype {:nativeType "int","number","int","byte"} C = x | 0 <= x < 256  // int

newtype {:nativeType "reallylong"} O = x | 0 <= x < 3000  // error: "reallylong" unknown
newtype {:nativeType "int","reallylong"} P = x | 0 <= x < 3000  // error: "reallylong" unknown

newtype {:nativeType "number"} Q = x | 0 <= x < 3000  // error: "number" not supported by C#
newtype {:nativeType "number","number"} R = x | 0 <= x < 3000  // error: "number" not supported by C#

newtype G = x | x < 30  // no native type, but that's okay
newtype {:nativeType} H = x | x < 30  // error: no native type, but one was requested
newtype {:nativeType} I = x | -2 <= x < 30  // sbyte
newtype {:nativeType true} J = x | x < 30  // error: no native type, but one was requested
newtype {:nativeType true} K = x | -2 <= x < 30  // sbyte

newtype {:nativeType false} E = x | x < 30  // no native type, and that's just as well
newtype {:nativeType false} F = x | -2 <= x < 30  // there is a native type, but they don't want it

newtype {:nativeType "int",false,"int"} PP = x | x == 16  // error: bad nativeType argument
newtype {:nativeType 3.14} QQ = x | x == 16  // error: bad nativeType argument
newtype {:nativeType "int"} RR = x: real | 0.0 <= x <= 3.0  // error: not integer type

newtype {:nativeType "long"} AA = int  // error: not a long
newtype {:nativeType "long"} BB = AA  // error: not a long
newtype {:nativeType "long"} CC = x: BB | -20 <= x < 20
newtype {:nativeType "long"} DD = CC
newtype {:nativeType "int"} EE = DD
newtype FF = EE  // sbyte
newtype {:nativeType "byte"} GG = EE  // error: not a byte
