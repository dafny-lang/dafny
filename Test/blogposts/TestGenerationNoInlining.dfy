// RUN: cp %S/TestGenerationNoInlining.dfy %t.dfy

// Generating and Running Block-Based Tests:
// RUN: %baredafny generate-tests %args Block %t.dfy > %t-tests.dfy
// RUN: %baredafny test %args --unicode-char:false --target:cs "%t-tests.dfy" >> "%t"

// Generating and Running Path-Based Tests:
// RUN: %baredafny generate-tests %args Path %t.dfy > %t-tests.dfy
// RUN: %baredafny test %args --unicode-char:false --target:cs "%t-tests.dfy" >> "%t"

// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*Dafny program verifier finished with 2 verified, 0 errors*
// CHECK: .*Evaluating the position: checked=no, checkmate=no*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes*
// CHECK: .*Dafny program verifier finished with 3 verified, 0 errors*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes*
// CHECK: .*Evaluating the position: checked=yes, checkmate=no*
// CHECK: .*Evaluating the position: checked=no, checkmate=no*

module Chess {
  datatype Color = Black | White
  datatype PieceKind = Knight(c: Color) | King(c: Color) | Pawn(c: Color)
  datatype Pos = Pos(row: int, col: int)
  type ChessPos = pos: Pos | // In this declaration, "|" means "such that" 
    && 0 <= pos.row < 8
    && 0 <= pos.col < 8 witness Pos(0, 0) // "witness" proves that the type is nonempty
  
  datatype Piece = Piece(kind: PieceKind, at: ChessPos) {
    predicate Attacks(pos: ChessPos) {
      && at != pos
      && match this.kind {
        case Knight(c) =>
          || ( && abs(pos.col - at.col) == 2
               && abs(pos.row - at.row) == 1)
          || ( && abs(pos.col - at.col) == 1
               && abs(pos.row - at.row) == 2)
        case King(c) => abs(pos.col - at.col) < 2 && abs(pos.row - at.row) < 2
        case Pawn(c) =>
          && pos.row == at.row + (if c.White? then -1 else 1)
          && (pos.col == at.col + 1 || pos.col == at.col - 1)
      }
    }
  }
  function abs(n: int): nat { if n > 0 then n else -n }

  datatype Board = Board(pieces: seq<Piece>) 
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
