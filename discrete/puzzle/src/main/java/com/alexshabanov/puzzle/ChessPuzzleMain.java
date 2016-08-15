package com.alexshabanov.puzzle;

import com.alexshabanov.puzzle.chess.StandardRank;
import com.alexshabanov.puzzle.chess.StandardSuit;
import com.alexshabanov.puzzle.chess.support.StandardPiece;
import com.alexshabanov.puzzle.chess.util.PrettyPrinter;

/**
 * @author Alexander Shabanov
 */
public final class ChessPuzzleMain {

  public static void main(String[] args) {
    PrettyPrinter.printDemo();

    System.out.println("White king symbol = " +
        PrettyPrinter.getPieceChar(StandardPiece.valueOf(StandardRank.KING, StandardSuit.BLACK)));
  }
}
