class _dafny:
    def print(self, toPrintVal):
        if type(toPrintVal)== bool:
            print("true" if toPrintVal else "false")
helpers = _dafny()