// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 4, N queens
// Rustan Leino, 31 August 2010, updated 24 March 2011.
//
// In the version of this program that I wrote during the week of VSTTE 2010, I had
// an unproved assumption.  In this version, I simply changed the existential quantifier
// in that assumption to specify a particular witness, which is enough of a hint for
// Dafny to fully prove the correctness of the program.
//
// Oh, I also added some comments in this version of the program.
//
// The correctness of this program relies on some properties of Queens boards.  These
// are stated and proved as lemmas, which here are given in assert statements.
//
// There is an annoyance in this program.  Dafny's proof-term representation of the function
// 'IsConsistent' implicitly takes the heap as an argument, despite the fact that
// 'IsConsistent' does not depend on any part of the heap.  Dafny ought to be able
// to figure that out from the fact that 'IsConsistent' has no 'reads' clause.
// Maybe a future version of Dafny will do just that.  But until then, some methods
// below are specified with an (easy-to-prove) postcondition that 'IsConsistent(B,p)'
// does not change for any 'B' and 'p', even if the method may change the heap in
// some way.
//
// The March 2011 update of this program was to make use of Dafny's new heuristics for
// compiling quantifiers.  This makes it possible to call IsConsistent, whose body uses
// a universal quantifier, from non-ghost code, which simplifies this program.


// The Search method returns whether or not there exists an N-queens solution for the
// given N.  If 'success' returns as 'true', 'board' indicates a solution.  If 'success'
// returns as 'false', no solution exists, as stated in the second postcondition.
method Search(N: int) returns (success: bool, board: seq<int>)
  requires 0 <= N;
  ensures success ==>
              |board| == N &&
              (forall p :: 0 <= p && p < N ==> IsConsistent(board, p));
  ensures !success ==>
              (forall B: seq<int> ::
                  |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N)
                  ==>
                  (exists p :: 0 <= p && p < N && !IsConsistent(B, p)));
{
  success, board := SearchAux(N, []);
}

// Given a board, this function says whether or not the queen placed in column 'pos'
// is consistent with the queens placed in columns to its left.
function method IsConsistent(board: seq<int>, pos: int): bool
{
  0 <= pos && pos < |board| &&
  (forall q :: 0 <= q && q < pos ==>
      board[q] != board[pos] &&
      board[q] - board[pos] != pos - q &&
      board[pos] - board[q] != pos - q)
}

// Here comes the method where the real work is being done.  With an ultimate board size of 'N'
// in mind and given the consistent placement 'boardSoFar' of '|boardSoFar|' columns, this method
// will search for a solution for the remaining columns.  If 'success' returns as 'true',
// then 'newBoard' is a consistent placement of 'N' queens.  If 'success' returns as 'false',
// then there is no way to extend 'boardSoFar' to get a solution for 'N' queens.
method SearchAux(N: int, boardSoFar: seq<int>) returns (success: bool, newBoard: seq<int>)
  requires 0 <= N && |boardSoFar| <= N;
  // consistent so far:
  requires (forall k :: 0 <= k && k < |boardSoFar| ==> IsConsistent(boardSoFar, k));
  ensures success ==>
              |newBoard| == N &&
              (forall p :: 0 <= p && p < N ==> IsConsistent(newBoard, p));
  ensures !success ==>
              (forall B: seq<int> ::
                  |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N) &&
                  boardSoFar <= B
                  ==>
                  (exists p :: 0 <= p && p < N && !IsConsistent(B, p)));
  decreases N - |boardSoFar|;
{
  var pos := |boardSoFar|;
  if (pos == N) {
    // The given board already has the desired size.
    newBoard := boardSoFar;
    success := true;
  } else {
    // Exhaustively try all possibilities for the new column, 'pos'.
    var n := 0;
    while (n < N)
      invariant n <= N;
      invariant (forall B: seq<int> ::
                  // For any board 'B' with 'N' queens, each placed in an existing row
                  |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N) &&
                  // ... where 'B' is an extension of 'boardSoFar'
                  boardSoFar <= B &&
                  // ... and the first column to extend 'boardSoFar' has a queen in one of
                  // the first 'n' rows
                  0 <= B[pos] && B[pos] < n
                  ==>
                  // ... the board 'B' is not entirely consistent
                  (exists p :: 0 <= p && p < N && !IsConsistent(B, p)));
    {
      // Let's try to extend the board-so-far with a queen in column 'n':
      var candidateBoard := boardSoFar + [n];
      if (IsConsistent(candidateBoard, pos)) {
        // The new queen is consistent.  Thus, 'candidateBoard' is consistent in column 'pos'.
        // The consistency of the queens in columns left of 'pos' follows from the
        // consistency of those queens in 'boardSoFar' and the fact that 'candidateBoard' is
        // an extension of 'boardSoFar', as the following lemma tells us:
        assert (forall k ::
                  0 <= k && k < |boardSoFar| && IsConsistent(boardSoFar, k)
                  ==>
                  IsConsistent(candidateBoard, k));

        // Thus, we meet the precondition of 'SearchAux' on 'candidateBoard', so let's search
        // for a solution that extends 'candidateBoard'.
        var s, b := SearchAux(N, candidateBoard);
        if (s) {
          // The recursive call to 'SearchAux' found consistent positions for all remaining columns
          newBoard := b;
          success := true;
          return;
        }
        // The recursive call to 'SearchAux' determined that no consistent extensions to 'candidateBoard'
        // exist.
      } else {
        // Since 'n' is not a consistent placement for a queen in column 'pos', there is also
        // no extension of 'candidateBoard' that would make the entire board consistent.
        assert (forall B: seq<int> ::
                  |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N) &&
                  candidateBoard <= B
                  ==>
                  !IsConsistent(B, pos));
      }
      n := n + 1;
    }

    success := false;
  }
}

method Main()
{
  var s, b := Search(2);
  print "N=2 returns ", s, "\n";
  s, b := Search(4);
  print "N=4 returns ", s, "\n";
  PrintSeq(b);
}

method PrintSeq(b: seq<int>)
{
  var i := 0;
  while (i < |b|) {
    print "  ", b[i], "\n";
    i := i + 1;
  }
}
