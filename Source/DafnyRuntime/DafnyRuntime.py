class _dafny:
    def printLiteralExpr(self,literalVal):
        return "true" if literalVal == True else "false"
helpers = _dafny()