import builtins

def print(value):
  if isinstance(value, bool):
    builtins.print("true" if value else "false", end="")
  elif isinstance(value, property):
    builtins.print(value.fget(), end="")
  else:
    builtins.print(value, end="")
