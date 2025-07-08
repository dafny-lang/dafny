
// Generating and Running Block-Based Tests:
// RUN: %baredafny generate-tests %args Block %S/TestGenerationNoInliningEnumerativeDefinitions.dfy > %t-tests.dfy
// RUN: %baredafny test %args --target:cs "%t-tests.dfy" > "%t"

// Generating and Running Path-Based Tests:
// RUN: %baredafny generate-tests %args Path %S/TestGenerationNoInliningEnumerativeDefinitions.dfy > %t-tests.dfy
// RUN: %baredafny test %args --target:cs "%t-tests.dfy" >> "%t"

// Syntactically, the test method has 4 paths: yes-yes, yes-no, no-yes, no-no. But the no-yes path is
// not feasible.
// When aiming for Block test coverage, using tests for the yes-yes and no-no paths is both
// sufficient and necessary. However, if the verifier happens to explore the yes-no path first, then
// the test generator will generate 3 tests instead of just 2, which is fine.
// Also, for both Block and Path test coverage, the order in which the tests are generated depends on what
// the verifier chooses to do first. Thus, if something changes in the verifier, then the CHECK lines below
// may need to be permuted.
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*Dafny program verifier finished with 2 verified, 0 errors.*
// CHECK: .*Evaluating the position: checked=no, checkmate=no.*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes.*
// CHECK: .*Dafny program verifier finished with 3 verified, 0 errors.*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes.*
// CHECK: .*Evaluating the position: checked=yes, checkmate=no.*
// CHECK: .*Evaluating the position: checked=no, checkmate=no.*

include "Inputs/TestGenerationShared.dfy"

module Chess {
  import opened Shared
  predicate BoardIsValid(board: Board) { 
    // We want boards with specific pieces on it:
    && |board.pieces| == 5
    && board.pieces[0].kind == King(White) 
    && board.pieces[1].kind == Knight(Black) && board.pieces[2].kind == Knight(Black)
    && board.pieces[3].kind == Pawn(Black)   && board.pieces[4].kind == Pawn(Black)
    // No two pieces on a single square:
    && board.pieces[0].at != board.pieces[1].at && board.pieces[0].at != board.pieces[2].at && board.pieces[0].at != board.pieces[3].at && board.pieces[0].at != board.pieces[4].at 
    && board.pieces[1].at != board.pieces[2].at && board.pieces[1].at != board.pieces[3].at && board.pieces[1].at != board.pieces[4].at 
    && board.pieces[2].at != board.pieces[3].at && board.pieces[2].at != board.pieces[4].at 
    && board.pieces[3].at != board.pieces[4].at
  }
  type ValidBoard = board: Board | BoardIsValid(board) 
    witness Board([Piece(King(White), Pos(0, 0)), 
                  Piece(Knight(Black), Pos(0, 1)), Piece(Knight(Black), Pos(0, 2)),
                  Piece(Pawn(Black), Pos(0, 3)),   Piece(Pawn(Black), Pos(0, 4))])
  predicate CheckedByPlayer(board: ValidBoard, king: Piece, byPlayer: Color) {
    || CheckedByPiece(board, king, Knight(byPlayer)) 
    || CheckedByPiece(board, king, Pawn(byPlayer))
  }
  predicate CheckedByPiece(board: ValidBoard, king: Piece, byPiece: PieceKind) {
    match byPiece {
      case Knight(Black) => board.pieces[1].Attacks(king.at) || board.pieces[2].Attacks(king.at)
      case Pawn(Black) => board.pieces[3].Attacks(king.at) || board.pieces[4].Attacks(king.at)
      case _ => false
    } 
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
  method {:testEntry} Describe(board: ValidBoard) {
    var whiteKing := board.pieces[0];
    print("Evaluating the position: ");
    if CheckedByPlayer(board, whiteKing, Black) {
      print("checked=yes, ");
    } else {
      print("checked=no, ");
    }
    if CheckmatedByPlayer(board, whiteKing, Black) {
      print("checkmate=yes\n");
    } else {
      print("checkmate=no\n"); 
    }
  }
}
