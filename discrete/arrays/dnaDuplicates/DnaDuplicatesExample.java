import java.util.HashMap;
import java.util.Map;

/**
 * Sample run:
 * <pre>
 * DNA=AAGGTT, duplicates={}
 * DNA=AAAGTATGAATATGGATT, duplicates={TAT=2, ATG=2}
 * DNA=GAATTGAATTAAA, duplicates={GAAT=2, AATT=2}
 * </pre>
 * @author Alexander Shabanov
 */
public final class DnaDuplicatesExample {

  public static void main(String[] args) {
    demo("AAGGTT", 2);
    demo("AAAGTATGAATATGGATT", 3);
    demo("GAATTGAATTAAA", 4);
  }

  public static void demo(String dna, int duplicateSize) {
    System.out.println("DNA=" + dna + ", duplicates=" + getDuplicates(dna.toCharArray(), duplicateSize));
  }

  // memory-greedy version

  public static Map<CharSequence, Integer> getDuplicates(char[] sequence, int duplicateSize) {
    final Map<CharSequence, Integer> entries = new HashMap<>();
    final int length = sequence.length - duplicateSize;
    for (int i = 0; i < length; ++i) {
      final CharBufferSlice slice = new CharBufferSlice(sequence, i, duplicateSize);
      entries.compute(slice, (charSequence, value) -> value == null ? 1 : (value + 1));
    }

    // return result and remove unique entries
    final Map<CharSequence, Integer> result = new HashMap<>();
    for (final Map.Entry<CharSequence, Integer> entry : entries.entrySet()) {
      if (entry.getValue() == 1) {
        continue;
      }
      result.put(entry.getKey(), entry.getValue());
    }
    return result;
  }

  /**
   * Helper class that represents a slice in char array.
   */
  private static final class CharBufferSlice implements CharSequence {
    private final char[] buf;
    private final int offset;
    private final int length;

    public CharBufferSlice(char[] buf, int offset, int length) {
      if (buf == null || offset < 0 || length < 0 || (offset + length) > buf.length) {
        throw new IllegalArgumentException();
      }
      this.buf = buf;
      this.offset = offset;
      this.length = length;
    }

    @Override
    public int length() {
      return length;
    }

    @Override
    public char charAt(int index) {
      return buf[offset + checkIndex(index)];
    }

    @Override
    public CharSequence subSequence(int start, int end) {
      if (start > end) {
        throw new IllegalArgumentException();
      }
      checkIndex(start);
      checkIndex(end);
      return new CharBufferSlice(buf, offset + start, end - start);
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof CharBufferSlice)) return false;

      CharBufferSlice charBufferSlice = (CharBufferSlice) o;

      if (charBufferSlice.length != length()) {
        return false;
      }

      for (int i = 0; i < length; ++i) {
        if (buf[offset + i] != charBufferSlice.buf[offset + i]) {
          return false;
        }
      }

      return true;
    }

    @Override
    public int hashCode() {
      int result = 0;
      for (int i = 0; i < length; ++i) {
        char ch = buf[offset + i];
        result += result * 31 + ch;
      }
      return result;
    }

    @SuppressWarnings("NullableProblems")
    @Override
    public String toString() {
      return new String(buf, offset, length);
    }

    private int checkIndex(int index) {
      if (index < 0 || index >= length) {
        throw new IndexOutOfBoundsException();
      }
      return index;
    }
  }
}
