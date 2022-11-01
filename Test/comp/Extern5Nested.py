"""
The Python compiler only supports {:extern} code on a module level, so the
entire module must be supplied.
"""

import sys

assert "Nested.Library" == __name__
Nested_Library = sys.modules[__name__]

class default__:
    def Foo():
        print("Nested.Library.Foo\n")
