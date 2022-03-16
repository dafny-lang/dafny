class _dafny:
    def print(value):
        if type(value) == bool:
            print("true" if value else "false", end="")
        else:
            print(value, end="")
