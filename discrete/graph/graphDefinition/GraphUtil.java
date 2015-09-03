/**
 * @author Alexander Shabanov
 */
public final class GraphUtil {
  private GraphUtil() {} // hidden

  public static String asString(UnidirectionalGraph graph) {
    final StringBuilder builder = new StringBuilder(graph.getVertexCount() * 20);
    final int spaces = 2;

    for (int i = 0; i < spaces; ++i) {
      builder.append(' ');
    }

    builder.append('|');
    for (int i = 0; i < graph.getVertexCount(); ++i) {
      builder.append(' ');
      appendAligned(builder, spaces, i);
    }
    builder.append('\n');

    for (int i = 0; i < spaces; ++i) {
      builder.append('-');
    }
    builder.append('+');
    for (int i = 0; i < graph.getVertexCount(); ++i) {
      builder.append('-');
      for (int j = 0; j < spaces; ++j) {
        builder.append('-');
      }
    }
    builder.append('\n');

    for (int i = 0; i < graph.getVertexCount(); ++i) {
      appendAligned(builder, spaces, i);
      builder.append('|');
      for (int j = 0; j < graph.getVertexCount(); ++j) {
        builder.append(' ');
        appendAligned(builder, spaces, graph.isConnected(i, j) ? 1 : 0);
      }
      builder.append('\n');
    }

    return builder.toString();
  }

  private static void appendAligned(StringBuilder builder, int spaces, int number) {
    int leadingSpaces = spaces - 1;
    int c = number;
    for (;;) {
      c = c / 10;
      if (c == 0) {
        break;
      }
      --leadingSpaces;
    }

    for (int i = 0; i < leadingSpaces; ++i) {
      builder.append(' ');
    }
    builder.append(number);
  }
}
