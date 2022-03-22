import builtins

def print(value):
  if type(value) == bool:
    builtins.print("true" if value else "false", end="")
  elif type(value) == property:
    builtins.print(value.fget(), end="")
  else:
    builtins.print(value, end="")