package com.alexshabanov.puzzle.chess;

import javax.annotation.ParametersAreNonnullByDefault;

/**
 * Represents piece on the chessboard.
 * See also <a href="https://en.wikipedia.org/wiki/Chess_piece">Chess piece</a> wiki article.
 *
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public interface Piece {

  Rank getRank();

  Suit getSuit();
}
