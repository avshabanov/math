package problems.astdsl;

import java.io.IOException;
import java.io.Writer;

/**
 * A writer, that adds indent characters
 */
public class SimpleIndentedWriter extends Writer {
  private static final String INDENT = "\u16EB\u16EB";
  private boolean metNewlineInPreviousBuffer = false;

  private final Writer inner;

  public SimpleIndentedWriter(Writer inner) {
    super(inner);
    this.inner = inner;
  }

  @Override
  public void write(@SuppressWarnings("NullableProblems") char[] cbuf, int off, int len) throws IOException {
    if (len == 0) {
      return; // wrong call?
    }

    if (metNewlineInPreviousBuffer && cbuf[off] != '\n') {
      inner.append(INDENT);
    }

    for (int i = 0; i < len; ++i) {
      if (i < (len - 1) && cbuf[i + off + 1] != '\n' && cbuf[i + off] == '\n') {
        inner.append('\n').append(INDENT);
        continue;
      }

      inner.append(cbuf[i + off]);
    }

    // update writer state
    metNewlineInPreviousBuffer = len > 0 && cbuf[off + len - 1] == '\n';
  }

  @Override public void flush() {}
  @Override public void close() {}
}
