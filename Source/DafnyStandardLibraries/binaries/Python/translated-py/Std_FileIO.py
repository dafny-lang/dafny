import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Std_Wrappers
import Std_BoundedInts
import Std_Base64
import Std_Relations
import Std_Math
import Std_Collections_Seq
import Std_Collections_Array
import Std_Collections_Imap
import Std_Functions
import Std_Collections_Iset
import Std_Collections_Map
import Std_Collections_Set
import Std_Collections
import Std_DynamicArray

# Module: Std_FileIO

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ReadBytesFromFile(path):
        res: Std_Wrappers.Result = Std_Wrappers.Result.default(_dafny.Seq)()
        d_111_isError_: bool
        d_112_bytesRead_: _dafny.Seq
        d_113_errorMsg_: _dafny.Seq
        out1_: bool
        out2_: _dafny.Seq
        out3_: _dafny.Seq
        out1_, out2_, out3_ = Std_PythonFileIOInternalExterns.default__.INTERNAL__ReadBytesFromFile(path)
        d_111_isError_ = out1_
        d_112_bytesRead_ = out2_
        d_113_errorMsg_ = out3_
        res = (Std_Wrappers.Result_Failure(d_113_errorMsg_) if d_111_isError_ else Std_Wrappers.Result_Success(d_112_bytesRead_))
        return res
        return res

    @staticmethod
    def WriteBytesToFile(path, bytes):
        res: Std_Wrappers.Result = Std_Wrappers.Result.default(_dafny.defaults.tuple())()
        d_114_isError_: bool
        d_115_errorMsg_: _dafny.Seq
        out4_: bool
        out5_: _dafny.Seq
        out4_, out5_ = Std_PythonFileIOInternalExterns.default__.INTERNAL__WriteBytesToFile(path, bytes)
        d_114_isError_ = out4_
        d_115_errorMsg_ = out5_
        res = (Std_Wrappers.Result_Failure(d_115_errorMsg_) if d_114_isError_ else Std_Wrappers.Result_Success(()))
        return res
        return res

