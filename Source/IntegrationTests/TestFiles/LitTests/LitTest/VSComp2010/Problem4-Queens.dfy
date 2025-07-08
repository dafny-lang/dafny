// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

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
// The March 2011 update of this program was to make use of Dafny's new heuristics for
// compiling quantifiers.  This makes it possible to call IsConsistent, whose body uses
// a universal quantifier, from non-ghost code, which simplifies this program.
//
// The October 2023 update of this program uses some features that were added long ago,
// like a datatype, a "for" loop, the "nat" type, chaining expressions, and if guards
// without parentheses. It also adds a nicer print method that displays the board.

datatype Option<X> = None | Some(value: X)

// The Search method returns whether or not there exists an N-queens solution for the
// given N.  If 'success' returns as 'true', 'board' indicates a solution.  If 'success'
// returns as 'false', no solution exists, as stated in the second postcondition.
method Search(N: nat) returns (r: Option<seq<int>>)
  ensures r.Some? ==> var board := r.value;
    |board| == N && forall p :: 0 <= p < N ==> IsConsistent(board, p)
  ensures r == None ==>
    forall B: seq<int> ::
      |B| == N && (forall i :: 0 <= i < N ==> 0 <= B[i] < N)
      ==>
      exists p :: 0 <= p < N && !IsConsistent(B, p)
{
  r := SearchAux(N, []);
}

// Given a board, this function says whether or not the queen placed in column 'pos'
// is consistent with the queens placed in columns to its left.
predicate IsConsistent(board: seq<int>, pos: nat) {
  pos < |board| &&
  forall q :: 0 <= q < pos ==>
    board[q] != board[pos] &&
    board[q] - board[pos] != pos - q &&
    board[pos] - board[q] != pos - q
}

// Here comes the method where the real work is being done.  With an ultimate board size of 'N'
// in mind and given the consistent placement 'boardSoFar' of '|boardSoFar|' columns, this method
// will search for a solution for the remaining columns.  If 'success' returns as 'true',
// then 'newBoard' is a consistent placement of 'N' queens.  If 'success' returns as 'false',
// then there is no way to extend 'boardSoFar' to get a solution for 'N' queens.
method SearchAux(N: nat, boardSoFar: seq<int>) returns (r: Option<seq<int>>)
  requires |boardSoFar| <= N
  // consistent so far:
  requires forall k :: 0 <= k < |boardSoFar| ==> IsConsistent(boardSoFar, k)
  ensures r.Some? ==> var newBoard := r.value;
    |newBoard| == N && forall p :: 0 <= p < N ==> IsConsistent(newBoard, p)
  ensures r == None ==>
    forall B: seq<int> ::
      |B| == N && (forall i :: 0 <= i < N ==> 0 <= B[i] < N) &&
      boardSoFar <= B
      ==>
      exists p :: 0 <= p < N && !IsConsistent(B, p)
  decreases N - |boardSoFar|
{
  var pos := |boardSoFar|;
  if pos == N {
    // The given board already has the desired size.
    return Some(boardSoFar);
  }

  // Exhaustively try all possibilities for the new column, 'pos'.
  for n := 0 to N
    invariant forall B: seq<int> ::
      // For any board 'B' with 'N' queens, each placed in an existing row
      |B| == N && (forall i :: 0 <= i < N ==> 0 <= B[i] < N) &&
      // ... where 'B' is an extension of 'boardSoFar'
      boardSoFar <= B &&
      // ... and the first column to extend 'boardSoFar' has a queen in one of
      // the first 'n' rows
      0 <= B[pos] < n
      ==>
      // ... the board 'B' is not entirely consistent
      exists p :: 0 <= p < N && !IsConsistent(B, p)
  {
    // Let's try to extend the board-so-far with a queen in column 'n':
    var candidateBoard := boardSoFar + [n];
    if IsConsistent(candidateBoard, pos) {
      // The new queen is consistent.  Thus, 'candidateBoard' is consistent in column 'pos'.
      // The consistency of the queens in columns left of 'pos' follows from the
      // consistency of those queens in 'boardSoFar' and the fact that 'candidateBoard' is
      // an extension of 'boardSoFar', as the following lemma tells us:
      assert forall k ::
        0 <= k < |boardSoFar| && IsConsistent(boardSoFar, k)
        ==>
        IsConsistent(candidateBoard, k);

      // Thus, we meet the precondition of 'SearchAux' on 'candidateBoard', so let's search
      // for a solution that extends 'candidateBoard'.
      r := SearchAux(N, candidateBoard);
      if r.Some? {
        // The recursive call to 'SearchAux' found consistent positions for all remaining columns
        return r;
      }
      // The recursive call to 'SearchAux' determined that no consistent extensions to 'candidateBoard'
      // exist.
    } else {
      // Since 'n' is not a consistent placement for a queen in column 'pos', there is also
      // no extension of 'candidateBoard' that would make the entire board consistent.
      assert forall B: seq<int> ::
        |B| == N && (forall i :: 0 <= i < N ==> 0 <= B[i] < N) &&
        candidateBoard <= B
        ==>
        !IsConsistent(B, pos);
    }
  }

  return None;
}

method Main() {
  SearchAndPrint(2);
  SearchAndPrint(4);
  SearchAndPrint(9);
}

method SearchAndPrint(N: nat) {
  var r := Search(N);
  print "N=", N, " returns ", r.Some?, "\n";
  if r.Some? {
    PrintBoard(r.value);
  }
}

method PrintBoard(b: seq<int>) {
  print "  +" + seq(|b|, _ => '-'), "+\n";
  for i := 0 to |b| {
    print "  |";
    for j := 0 to |b| {
      print if j == b[i] then "*" else " ";
    }
    print "| ", b[i], "\n";
  }
  print "  +" + seq(|b|, _ => '-'), "+\n";
}
