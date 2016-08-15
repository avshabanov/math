package com.alexshabanov.puzzle.chess.util;

import com.alexshabanov.puzzle.chess.*;

import javax.annotation.ParametersAreNonnullByDefault;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public final class PrettyPrinter {
  private PrettyPrinter() {} // hidden

  public static final String ANSI_RESET       = "\u001B[0m";

  public static final String ANSI_CL_BLACK    = "\u001B[30m";
  public static final String ANSI_CL_RED      = "\u001B[31m";
  public static final String ANSI_CL_GREEN    = "\u001B[32m";
  public static final String ANSI_CL_YELLOW   = "\u001B[33m";
  public static final String ANSI_CL_BLUE     = "\u001B[34m";
  public static final String ANSI_CL_PURPLE   = "\u001B[35m";
  public static final String ANSI_CL_CYAN     = "\u001B[36m";
  public static final String ANSI_CL_WHITE    = "\u001B[37m";

  public static final String ANSI_BG_BLACK    = "\u001B[40m";
  public static final String ANSI_BG_RED      = "\u001B[41m";
  public static final String ANSI_BG_GREEN    = "\u001B[42m";
  public static final String ANSI_BG_YELLOW   = "\u001B[43m";
  public static final String ANSI_BG_BLUE     = "\u001B[44m";
  public static final String ANSI_BG_PURPLE   = "\u001B[45m";
  public static final String ANSI_BG_CYAN     = "\u001B[46m";
  public static final String ANSI_BG_WHITE    = "\u001B[47m";

  public static final String ANSI_ATTR_BOLD   = "\u001B[1m";
  public static final String ANSI_ATTR_DARK   = "\u001B[2m";
  public static final String ANSI_ATTR_UNDERLINE = "\u001B[4m";
  public static final String ANSI_ATTR_REVERSE = "\u001B[7m";

  public static char getPieceChar(Piece piece) {
    final Suit suit = piece.getSuit();
    final Rank rank = piece.getRank();
    if (suit instanceof StandardSuit) {
      if (rank instanceof StandardRank) {
        return getSuitRankChar((StandardRank) rank, (StandardSuit) suit);
      }
    }

    throw new UnsupportedOperationException("Unsupported rank/suit for piece=" + piece);
  }

  public static void printDemo() {
    System.out.println(ANSI_CL_BLUE + ANSI_ATTR_UNDERLINE + ANSI_ATTR_BOLD + "Blue Text!" + ANSI_RESET);
    System.out.println(ANSI_ATTR_DARK + ANSI_BG_YELLOW + ANSI_CL_BLUE + "Another Blue Text!" + ANSI_RESET);
    System.out.println(ANSI_CL_RED + "Red Text!" + ANSI_RESET);
  }

  public static char getSuitRankChar(StandardRank rank, StandardSuit suit) {
    switch (rank) {
      case KING:
        return suit == StandardSuit.WHITE ? '\u2654' : '\u265A';

      case QUEEN:
        return suit == StandardSuit.WHITE ? '\u2655' : '\u265B';

      case ROOK:
        return suit == StandardSuit.WHITE ? '\u2656' : '\u265C';

      case BISHOP:
        return suit == StandardSuit.WHITE ? '\u2657' : '\u265D';

      case KNIGHT:
        return suit == StandardSuit.WHITE ? '\u2658' : '\u265E';

      case PAWN:
        return suit == StandardSuit.WHITE ? '\u2659' : '\u265F';
    }

    throw new IllegalArgumentException("Unknown combination of suit=" + suit + " and rank=" + rank);
  }
}
