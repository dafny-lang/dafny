import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny

# Module: System_

class nat:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

