"""
The Python compiler only supports {:extern} code on a module level, so the
entire module must be supplied.
"""

import sys, _dafny

assert "Nested.Library" == __name__
Nested_Library = sys.modules[__name__]

class default__:
    def Foo():
        _dafny.print(_dafny.Seq("Nested.Library.Foo\n"))