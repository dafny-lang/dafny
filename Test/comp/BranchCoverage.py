import sys

assert "DafnyProfiling" == __name__
DafnyProfiling = sys.modules[__name__]

class CodeCoverage:
    tallies = []

    @staticmethod
    def Setup(size):
        CodeCoverage.tallies = size*[0]

    @staticmethod
    def TearDown():
        for i, tally in enumerate(CodeCoverage.tallies):
            print(f'{i}: {tally}')
        CodeCoverage.tallies = []

    @staticmethod
    def Record(id):
        CodeCoverage.tallies[id] += 1
        return True
