// Generating and Running Path-Based Tests:
// RUN: %baredafny generate-tests %args Path %S/TestGenerationWithInliningQuantifiedDefinitions.dfy > %t-tests.dfy
// RUN: %baredafny test %args --target:cs "%t-tests.dfy" > "%t"

// Syntactically, the test method has 4 paths: yes-yes, yes-no, no-yes, no-no. But the no-yes path is
// not feasible.
// For Path test coverage, the order in which the tests are generated depends on what
// the verifier chooses to do first. Thus, if something changes in the verifier, then the CHECK lines below
// may need to be permuted.
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*Dafny program verifier finished with 5 verified, 0 errors*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes, pawn is attacking*
// CHECK: .*Evaluating the position: checked=yes, checkmate=no, pawn is attacking*
// CHECK: .*Evaluating the position: checked=no, checkmate=no*
// CHECK: .*Evaluating the position: checked=yes, checkmate=no, knight is attacking*

include "Inputs/TestGenerationShared.dfy"

module Chess {
  import opened Shared
  predicate BoardIsValid(board: Board) { // No two pieces on a single square
    forall i: nat, j: nat :: 
      0 <= i < j < |board.pieces| ==> 
      board.pieces[i].at != board.pieces[j].at
  }
  type ValidBoard = board: Board | BoardIsValid(board) witness Board([])
  predicate {:testInline 1} CheckedByPlayer(board: ValidBoard, king: Piece, byPlayer: Color) {
    || CheckedByPiece(board, king, Knight(byPlayer)) 
    || CheckedByPiece(board, king, Pawn(byPlayer))
  }
  predicate CheckedByPiece(board: ValidBoard, king: Piece, byPiece: PieceKind) {
    exists i: int :: (&& 0 <= i < |board.pieces| 
                      && board.pieces[i].kind == byPiece 
                      && board.pieces[i].Attacks(king.at))
  } by method {
    for i := 0 to |board.pieces| 
        invariant !CheckedByPiece(Board(board.pieces[..i]), king, byPiece) {
        if (board.pieces[i].kind == byPiece && 
            board.pieces[i].Attacks(king.at)) {
            return true;
        }
    }
    return false;
  } 
  predicate BoardPreset(board: Board) {
    && |board.pieces| == 5
    && board.pieces[0].kind == King(White) 
    && board.pieces[1].kind == Knight(Black) && board.pieces[2].kind == Knight(Black)
    && board.pieces[3].kind == Pawn(Black)   && board.pieces[4].kind == Pawn(Black)
  }
  predicate CheckmatedByPlayer(board: ValidBoard, king: Piece, byPlayer: Color) {
    && (king.at.row == 0 || king.at.col == 7 || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row - 1, king.at.col + 1)), byPlayer))
    && (                    king.at.col == 7 || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row,     king.at.col + 1)), byPlayer))
    && (king.at.row == 7 || king.at.col == 7 || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row + 1, king.at.col + 1)), byPlayer))
    && (king.at.row == 0                     || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row - 1, king.at.col)),     byPlayer))   
    &&                                          CheckedByPlayer(board, king, byPlayer)     
    && (king.at.row == 7                     || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row + 1, king.at.col)),     byPlayer))
    && (king.at.row == 0 || king.at.col == 0 || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row - 1, king.at.col - 1)), byPlayer))
    && (                 || king.at.col == 0 || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row,     king.at.col - 1)), byPlayer))
    && (king.at.row == 7 || king.at.col == 0 || CheckedByPlayer(board, Piece(king.kind, Pos(king.at.row + 1, king.at.col - 1)), byPlayer))
  }

  // {:testEntry} tells Dafny to use this method as an entry point
  method {:testEntry} Describe(board: ValidBoard) 
    requires BoardPreset(board)
  {
    var whiteKing := board.pieces[0];
    print("Evaluating the position: ");
    if CheckedByPlayer(board, whiteKing, Black) {
      print("checked=yes, ");
    } else {
      print("checked=no, ");
    }
    if CheckmatedByPlayer(board, whiteKing, Black) {
      print("checkmate=yes, ");
    } else {
      print("checkmate=no, "); 
    }
    Debug(board);
  }

  method Debug(board: ValidBoard) 
    requires BoardPreset(board)
  {
    var whiteKing := board.pieces[0];
    if CheckedByPiece(board, whiteKing, Knight(Black)) {
      print("knight is attacking\n");
    } else if CheckedByPiece(board, whiteKing, Pawn(Black)) {
      print("pawn is attacking\n");
    } 
  }
}
