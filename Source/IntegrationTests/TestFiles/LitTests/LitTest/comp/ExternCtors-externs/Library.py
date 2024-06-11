import sys

import module_
import _dafny
import System_

assert "Library" == __name__
Library = sys.modules[__name__]

class Class:
    def __init__(self, n) -> None:
        self.n = n

    @staticmethod
    def SayHi():
        print("Hello!")

    def Get(self):
        return self.n

    def Print(self):
        _dafny.print(_dafny.string_of(_dafny.Seq("My value is ")))
        _dafny.print(_dafny.string_of((self).Get()))
        _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
