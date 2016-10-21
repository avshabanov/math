package ticTacToeSupport;

import java.util.Arrays;

/**
 * @author Alexander Shabanov
 */
public final class ArrayBasedField implements Field {
  private final Cell[] cells;
  private final int dim;

  public ArrayBasedField(int dim) {
    this.dim = dim;
    this.cells = new Cell[dim * dim];
    Arrays.fill(this.cells, Cell.EMPTY);
  }

  public ArrayBasedField() {
    this(3);
  }

  @Override
  public int getDimension() {
    return dim;
  }

  @Override
  public Cell cellAt(int w, int h) {
    return cells[w + h * dim];
  }

  @Override
  public Field setCell(int w, int h, Cell cell) {
    cells[w + h * dim] = cell;
    return this;
  }
}
