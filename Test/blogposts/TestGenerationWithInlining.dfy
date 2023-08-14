// RUN: cp %S/TestGenerationWithInlining.dfy %t.dfy

// Generating and Running Path-Based Tests:
// RUN: %baredafny generate-tests %args Path %t.dfy > %t-tests.dfy
// RUN: %baredafny test %args --unicode-char:false --target:cs "%t-tests.dfy" >> "%t"

// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: .*Dafny program verifier finished with 5 verified, 0 errors*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes, pawn is attacking*
// CHECK: .*Evaluating the position: checked=yes, checkmate=no, pawn is attacking*
// CHECK: .*Evaluating the position: checked=no, checkmate=no*
// CHECK: .*Evaluating the position: checked=yes, checkmate=yes, knight is attacking*
// CHECK: .*Evaluating the position: checked=yes, checkmate=no, knight is attacking*

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
