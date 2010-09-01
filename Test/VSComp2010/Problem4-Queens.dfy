// VSComp 2010, problem 4, N queens
// Rustan Leino, 31 August 2010.
//
// In the version of this program that I wrote during the week of VSTTE 2010, I had
// an unproved assumption.  In this version, I simply changed the existential quantifier
// in that assumption to specify a particular witness, which is enough of a hint for
// Dafny to fully prove the correctness of the program.
//
// Oh, I also added some comments in this version of the program.
//
// The correctness of this program relies on some properties of Queens boards.  These
// are stated and proved as lemmas, which can be declared in Dafny as ghost methods.
//
// There are two annoyances in this program:
//
// One has to do with Dafny's split between ''ghost'' variables/code and ''physical''
// variables/code.  The ''ghost'' things are used by the verifier, but are ignored by
// the compiler.  This is generally good, since any additional specifications are ghost
// state that are needed to convince the verifier that a program is correct (let alone
// express what it means for the program to be correct) are not required at run time.
// However, Dafny currently considers *all* quantifiers to be ghost-only, which
// necessitates some duplication of the 'IsConsistent' condition.
//
// The other annoyance is that Dafny's proof-term representation of the function
// 'IsConsistent' implicitly takes the heap as an argument, despite the fact that
// 'IsConsistent' does not depend on any part of the heap.  Dafny ought to be able
// to figure that out from the fact that 'IsConsistent' has no 'reads' clause.
// Maybe a future version of Dafny will do just that.  But until then, some methods
// below are specified with an (easy-to-prove) postcondition that 'IsConsistent(B,p)'
// does not change for any 'B' and 'p', even if the method may change the heap in
// some way.


// The Search method returns whether or not there exists an N-queens solution for the
// given N.  If 'success' returns as 'true', 'board' indicates a solution.  If 'success'
// returns as 'false', no solution exists, as stated in the second postcondition.
method Search(N: int) returns (success: bool, board: seq<int>)
  requires 0 <= N;
  ensures success ==>
              |board| == N &&
              (forall p :: 0 <= p && p < N ==> IsConsistent(board, p));
  ensures !success ==>
              (forall B ::
                  |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N)
                  ==>
                  (exists p :: 0 <= p && p < N && !IsConsistent(B, p)));
{
  call success, board := SearchAux(N, []);
}

// Given a board, this function says whether or not the queen placed in column 'pos'
// is consistent with the queens placed in columns to its left.
static function IsConsistent(board: seq<int>, pos: int): bool
{
  0 <= pos && pos < |board| &&
  (forall q :: 0 <= q && q < pos ==>
      board[q] != board[pos] &&
      board[q] - board[pos] != pos - q &&
      board[pos] - board[q] != pos - q)
}

// The following lemma says that 'IsConsistent' is monotonic in its first argument.
// More precisely, if 'short' is a board with a queen consistently placed in column
// 'pos', then that queen is also consistently placed in any extension 'long' of the
// board 'short' (that is, the sequence of queen positions 'short' is a prefix of the
// sequence of queen positions 'long').  In other words, consistency of a queen in
// column 'pos' does not depend on columns to the right of 'pos'.
ghost method Lemma0(short: seq<int>, long: seq<int>, pos: int)
  requires short <= long;
  ensures IsConsistent(short, pos) ==> IsConsistent(long, pos);
{
  if (IsConsistent(short, pos)) {
    assert IsConsistent(long, pos);
  }
}

// Lemma1 states Lemma0 for every column in the board 'short'.
ghost method Lemma1(short: seq<int>, long: seq<int>)
  requires short <= long;
  ensures (forall k :: 0 <= k && k < |short| && IsConsistent(short, k) ==> IsConsistent(long, k));
  ensures (forall B, p :: IsConsistent(B, p) <==> old(IsConsistent(B, p)));
{
  var j := 0;
  while (j < |short|)
    invariant j <= |short|;
    invariant (forall k :: 0 <= k && k < j && IsConsistent(short, k) ==> IsConsistent(long, k));
  {
    call Lemma0(short, long, j);
    j := j + 1;
  }
}

method CheckConsistent(board: seq<int>, pos: int) returns (b: bool)
  ensures b <==> IsConsistent(board, pos);
  ensures (forall B, p :: IsConsistent(B, p) <==> old(IsConsistent(B, p)));
{
  // The Dafny compiler won't compile a function with a 'forall' inside.  (This seems reasonable
  // in general, since quantifiers could range over all the integers.  Here, however, where the
  // range of the quantifier is bounded, it just seems stupid.)  Therefore, we
  // have to provide a method that computes the same thing as the function defines.
  if (0 <= pos && pos < |board|) {
    var p := 0;
    while (p < pos)
      invariant p <= pos;
      invariant (forall q :: 0 <= q && q < p ==>
                  board[q] != board[pos] &&
                  board[q] - board[pos] != pos - q &&
                  board[pos] - board[q] != pos - q);
    {
      if (!(board[p] != board[pos] &&
            board[p] - board[pos] != pos - p &&
            board[pos] - board[p] != pos - p)) {
        b := false;
        return;
      }
      p := p + 1;
    }
    b := true;
    return;
  }
  b := false;
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
              (forall B ::
                  |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N) &&
                  boardSoFar <= B
                  ==>
                  (exists p :: 0 <= p && p < N && !IsConsistent(B, p)));
  ensures (forall B, p :: IsConsistent(B, p) <==> old(IsConsistent(B, p)));
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
      invariant (forall B ::
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
      call consistent := CheckConsistent(candidateBoard, pos);
      if (consistent) {
        // The new queen is consistent.  Thus, 'candidateBoard' is consistent in column 'pos'.
        // The consistency of the queens in columns left of 'pos' follows from the
        // consistency of those queens in 'boardSoFar' and the fact that 'candidateBoard' is
        // an extension of 'boardSoFar', as Lemma1 tells us:
        call Lemma1(boardSoFar, candidateBoard);
        // Thus, we meet the precondition of 'SearchAux' on 'candidateBoard', so let's search
        // for a solution that extends 'candidateBoard'.
        call s, b := SearchAux(N, candidateBoard);
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
        assert (forall B ::
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
  call s, b := Search(2);
  print "N=2 returns ", s, "\n";
  call s, b := Search(4);
  print "N=4 returns ", s, "\n";
  call PrintSeq(b);
}

method PrintSeq(b: seq<int>)
{
  var i := 0;
  while (i < |b|) {
    print "  ", b[i], "\n";
    i := i + 1;
  }
}
