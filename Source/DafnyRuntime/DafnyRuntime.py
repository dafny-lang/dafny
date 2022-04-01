"""Runtime enabling Dafny language features."""
import builtins

class classproperty(property):
    def __get__(self, instance, owner):
        return classmethod(self.fget).__get__(None, owner)()

def print(value):
    if isinstance(value, bool):
        builtins.print("true" if value else "false", end="")
    else:
        builtins.print(value, end="")
