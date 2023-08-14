module Shared {
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
  datatype Board = Board(pieces:seq<Piece>)
}