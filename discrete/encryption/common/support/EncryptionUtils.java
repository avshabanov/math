package support;

/**
 * Utility functions for encryption functionality.
 */
public final class EncryptionUtils {
  private EncryptionUtils() {
  }

  public static int writeLong(byte[] bytes, int offset, long longValue) {
    for (int i = 7; i >= 0; i--) {
      bytes[offset + i] = (byte) (longValue & 0xffL);
      longValue >>= 8;
    }

    return offset + 8/* count of bytes written */;
  }

  public static int writeInt(byte[] bytes, int offset, int intValue) {
    for (int i = 3; i >= 0; i--) {
      bytes[offset + i] = (byte) (intValue & 0xff);
      intValue >>= 8;
    }

    return offset + 4/* count of bytes written */;
  }

  public static long longFromByteArray(byte[] bytes, int offset) {
    return longFromBytes(bytes[offset], bytes[offset + 1], bytes[offset + 2], bytes[offset + 3],
        bytes[offset + 4], bytes[offset + 5], bytes[offset + 6], bytes[offset + 7]) ;
  }

  public static long longFromBytes(byte b1, byte b2, byte b3, byte b4,
                                    byte b5, byte b6, byte b7, byte b8) {
    return (b1 & 0xFFL) << 56
        | (b2 & 0xFFL) << 48
        | (b3 & 0xFFL) << 40
        | (b4 & 0xFFL) << 32
        | (b5 & 0xFFL) << 24
        | (b6 & 0xFFL) << 16
        | (b7 & 0xFFL) << 8
        | (b8 & 0xFFL);
  }

  public static int intFromByteArray(byte[] bytes, int offset) {
    return intFromBytes(bytes[offset], bytes[offset + 1], bytes[offset + 2], bytes[offset + 3]) ;
  }

  public static int intFromBytes(byte b1, byte b2, byte b3, byte b4) {
    return (b1 & 0xFF) << 24
        | (b2 & 0xFF) << 16
        | (b3 & 0xFF) << 8
        | (b4 & 0xFF);
  }

  public static int ror(int x, int shift) {
    return (x >>> shift) | ((x & ((1 << shift) - 1)) << (32 - shift));
  }

  public static int rol(int x, int shift) {
    return (x << shift) | (((x >>> (32 - shift)) & ((1 << shift) - 1)));
  }
}
