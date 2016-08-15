package com.alexshabanov.puzzle.chess.support;

import com.alexshabanov.puzzle.chess.Piece;
import com.alexshabanov.puzzle.chess.Rank;
import com.alexshabanov.puzzle.chess.Suit;

import javax.annotation.ParametersAreNonnullByDefault;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public class StandardPiece implements Piece {
  private final Rank rank;
  private final Suit suit;

  private StandardPiece(Rank rank, Suit suit) {
    this.rank = rank;
    this.suit = suit;
  }

  public static StandardPiece valueOf(Rank rank, Suit suit) {
    return new StandardPiece(rank, suit);
  }

  @Override
  public Rank getRank() {
    return rank;
  }

  @Override
  public Suit getSuit() {
    return suit;
  }

  @Override
  public String toString() {
    return "@(" + getSuit() + ' ' + getRank() + ')';
  }
}
