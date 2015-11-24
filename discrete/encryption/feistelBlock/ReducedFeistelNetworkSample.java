
/**
 * Sample output (note completely different cypher text for slightly different inputs):
 *
 * <pre>
 * src=0x               1, key=0x               1, enc=0x29DF77535CBCF4A1, dec=0x               1
 * src=0x               1, key=0x               2, enc=0x20E769377BA06E80, dec=0x               1
 * src=0x               2, key=0x               1, enc=0x7A93570B20789D4D, dec=0x               2
 * src=0xFFFFFFFFFFFFFFFF, key=0x               1, enc=0x5C98BA6D503ED1C2, dec=0xFFFFFFFFFFFFFFFF
 * src=0xFFFFFFFFFFFFFFFE, key=0x               1, enc=0x639A57F321172DBF, dec=0xFFFFFFFFFFFFFFFE
 * src=0x               1, key=0xCC582491128C9BC3, enc=0x6C418427DE9E5592, dec=0x               1
 * src=0x               2, key=0xCC582491128C9BC3, enc=0x443394B4EA3557C9, dec=0x               2
 * src=0xFFFFFFFFFFFFFFFF, key=0xCC582491128C9BC3, enc=0xE9E8A13B204AE9C5, dec=0xFFFFFFFFFFFFFFFF
 * src=0xFFFFFFFFFFFFFFFE, key=0xCC582491128C9BC3, enc=0xD78A8960FF230777, dec=0xFFFFFFFFFFFFFFFE
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ReducedFeistelNetworkSample {

  public static void main(String[] args) {
    // compare when key and cyphertext are slightly different
    encryptDecrypt(1, 1);
    encryptDecrypt(1, 2);
    encryptDecrypt(2, 1);

    encryptDecrypt(-1, 1);
    encryptDecrypt(-2, 1);


    encryptDecrypt( 1, 0xcc582491128c9bc3L/* Random key */);
    encryptDecrypt( 2, 0xcc582491128c9bc3L);
    encryptDecrypt(-1, 0xcc582491128c9bc3L);
    encryptDecrypt(-2, 0xcc582491128c9bc3L);
  }

  static void encryptDecrypt(long number, long key) {
    final long e = encrypt(number, key);
    System.out.println(String.format("src=0x%16X, key=0x%16X, enc=0x%16X, dec=0x%16X", number, key,
        e, decrypt(e, key)));
  }

  //
  // Private
  //

  private static final int NUM_ROUNDS = 16; /* Needs to be 16 to use all the places in keys for both left and right */

  private static final int MASKS[] = { /* Random numbers - masks */
      0xd588f962, 0xc9a72c6c, 0x33ebcf11, 0x18387278,
      0xc1593935, 0x3ef5b0e2, 0x7e0f147f, 0x4e39324d,
      0x744a95ad, 0x05aab3e4, 0xd8d2a9a4, 0x8d68820b,
      0xd045d5b4, 0x8f979bff, 0x0410ecd2, 0x3ad24146,
      0x46215586, 0xad834b0e, 0x62c572ab, 0x4c9b6c2e,
      0xf3ad4261, 0xcc1cfe62, 0x04925703, 0x78eb240e
  };

  private static final int ROTS[] = { /* Random numbers - shifts */
      3,  25, 7,  13,
      11, 21, 29, 7,
      28, 15, 4,  6,
      9,  19, 17, 2
  };

  /**
   * Sample of reduced feistel network built on top of long numbers
   *
   * @param text Source text
   * @param key Encryption key
   * @return Encrypted result
   */
  private static long encrypt(long text, long key) {
    int l = (int) (text & 0xFFFFFFFFL);
    int r = (int) (text >>> 32);

    int keyPart1 = (int) (key);
    int keyPart2 = (int) (key >>> 32);

    for (int i = 0; i < NUM_ROUNDS; ++i) {
      final int keyPart;
      if ((i & 1) == 0) {
        keyPart = keyPart1;
      } else {
        keyPart = keyPart2;
      }

      final int keyNum = ((keyPart + r) >> ((i % 8) * 4)) & 0xF;
      assert keyNum >= 0 && keyNum < ROTS.length && keyNum < MASKS.length;
      final int shift = ROTS[keyNum];
      final int mask = MASKS[keyNum];
      final int rNext = ror((l + keyPart) ^ mask, shift);
      //System.out.println(String.format("[D] r=%s, rNext=%s, keyNum=%s", r, rNext, keyNum));

      l = r;
      r = rNext;
    }

    return (((long) (l)) & 0xFFFFFFFFL) | (((long) r) << 32);
  }

  private static long decrypt(long enc, long key) {
    int l = (int) (enc & 0xFFFFFFFFL);
    int r = (int) (enc >>> 32);

    int keyPart1 = (int) (key);
    int keyPart2 = (int) (key >>> 32);

    for (int i = NUM_ROUNDS - 1; i >= 0; --i) {
      final int keyPart;
      if ((i & 1) == 0) {
        keyPart = keyPart1;
      } else {
        keyPart = keyPart2;
      }

      final int keyNum = ((keyPart + l) >> ((i % 8) * 4)) & 0xF;
      assert keyNum >= 0 && keyNum < ROTS.length && keyNum < MASKS.length;
      final int shift = ROTS[keyNum];
      final int mask = MASKS[keyNum];
      final int lNext = (rol(r, shift) ^ mask) - keyPart;
      //System.out.println(String.format("[D] l=%s, lNext=%s, keyNum=%s", l, lNext, keyNum));

      r = l;
      l = lNext;
    }

    return (long) (l) | (((long) r) << 32);
  }

  private static int ror(int x, int shift) {
    return (x >>> shift) | ((x & ((1 << shift) - 1)) << (32 - shift));
  }

  private static int rol(int x, int shift) {
    return (x << shift) | (((x >>> (32 - shift)) & ((1 << shift) - 1)));
  }
}
