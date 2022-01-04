class _dafny:
    def print(toPrintVal):
        if type(toPrintVal)== bool:
            print("true" if toPrintVal else "false")
        else:
            print(toPrintVal)