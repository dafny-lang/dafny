import sys

assert "BoxPkg" == __name__
BoxPkg = sys.modules[__name__]

# An extern class that overrides __eq__/__hash__ with structural equality
# (any two boxes are "equal"), subverting the identity equality Dafny's
# verifier assumes for classes.
class Box:
    def __init__(self) -> None:
        pass

    def __eq__(self, other):
        return isinstance(other, Box)

    def __hash__(self):
        return 0
