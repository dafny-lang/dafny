import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import _dafny as _dafny

# Module: System_

class nat:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        d_0_x_: int = source__
        return (0) <= (d_0_x_)

