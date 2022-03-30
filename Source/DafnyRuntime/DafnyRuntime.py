class _dafny:
  def print(value):
    if type(value) == bool:
      print("true" if value else "false", end="")
    elif type(value) == property:
      print(value.fget(), end="")
    else:
      print(value, end="")
