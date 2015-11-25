import static support.EncryptionUtils.rol;
import static support.EncryptionUtils.ror;

/**
 * Sample output (note completely different cypher text for slightly different inputs):
 *
 * <pre>
 * src=0x               1, key=0x               1, enc=0x785A2E98184A6E33, dec=0x               1
 * src=0x               2, key=0x               1, enc=0xC06A77ADA1354EBA, dec=0x               2
 * src=0x               3, key=0x               1, enc=0xE9C4C147FE4C4797, dec=0x               3
 * src=0x               1, key=0x               2, enc=0x15EA9CDD73EE0228, dec=0x               1
 * src=0xFFFFFFFFFFFFFFFF, key=0x               1, enc=0x750BFC7982DF53F4, dec=0xFFFFFFFFFFFFFFFF
 * src=0xFFFFFFFFFFFFFFFE, key=0x               1, enc=0xB7FB988CB5F179BC, dec=0xFFFFFFFFFFFFFFFE
 * src=0x               1, key=0xCC582491128C9BC3, enc=0xD9BE01CFCE0FCE0E, dec=0x               1
 * src=0x               2, key=0xCC582491128C9BC3, enc=0xC9490CA181F5B56A, dec=0x               2
 * src=0xFFFFFFFFFFFFFFFF, key=0xCC582491128C9BC3, enc=0xFA21566209E355F9, dec=0xFFFFFFFFFFFFFFFF
 * src=0xFFFFFFFFFFFFFFFE, key=0xCC582491128C9BC3, enc=0x7D83307420E355F9, dec=0xFFFFFFFFFFFFFFFE
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class ReducedFeistelNetworkSample {

  public static void main(String[] args) {
    // compare when key and cyphertext are slightly different
    encryptDecrypt(1, 1);
    encryptDecrypt(2, 1);
    encryptDecrypt(3, 1);

    encryptDecrypt(1, 2);

    encryptDecrypt(-1, 1);
    encryptDecrypt(-2, 1);

    final long key = 0xcc582491128c9bc3L/* Random key */;
    encryptDecrypt( 1, key);
    encryptDecrypt( 2, key);
    encryptDecrypt(-1, key);
    encryptDecrypt(-2, key);
  }

  static void encryptDecrypt(long number, long key) {
    final long e = encrypt(number, key);
    final long d = decrypt(e, key);
    if (number != d) {
      throw new AssertionError("Encrypt/Decrypt failed for number=" + number + ", key=" + key + ", enc=" + e);
    }
    System.out.println(String.format("src=0x%16X, key=0x%16X, enc=0x%16X, dec=0x%16X", number, key,
        e, d));
  }

  //
  // Private
  //

  static final int NUM_ROUNDS = 16; /* Needs to be 16 to use all the places in keys for both left and right */

  static final int MASKS[] = { /* Random numbers - masks */
      0x744a95ad, 0x05aab3e4, 0xd8d2a9a4, 0x8d68820b,
      0xd588f962, 0xc9a72c6c, 0x33ebcf11, 0x18387278,
      0xc1593935, 0x3ef5b0e2, 0x7e0f147f, 0x4e39324d,
      0xd045d5b4, 0x8f979bff, 0x0410ecd2, 0x3ad24146
  };

  static final int SHIFTS[] = { /* Random numbers - shifts */
      17, 16, 19, 2,
      5,  27, 23, 18,
      9,  7,  11, 3,
      29, 21, 28, 13
  };

  /**
   * Sample of reduced feistel network built on top of long numbers
   *
   * @param text Source text
   * @param key Encryption key
   * @return Encrypted result
   */
  private static long encrypt(long text, long key) {
    int l = (int) (text);
    int r = (int) (text >>> 32);

    int keyPart1 = (int) (key);
    int keyPart2 = (int) (key >>> 32);

    for (int i = 0; i < NUM_ROUNDS; ++i) {
      final int keyPart = ((i & 1) == 0) ? keyPart1 : keyPart2;
      final int keyNum = ((keyPart + r) >> ((i % 8) * 4)) & 0xF;
      assert keyNum >= 0 && keyNum < SHIFTS.length && keyNum < MASKS.length;
      final int shift = SHIFTS[keyNum];
      final int mask = MASKS[keyNum];
      final int rNext = ror((keyPart + l) ^ mask, shift);
      //System.out.println(String.format("[D] r=%s, rNext=%s, keyNum=%s", r, rNext, keyNum));

      l = r;
      r = rNext;
    }

    return (((long) (l)) & 0xFFFFFFFFL) | (((long) r) << 32);
  }

  private static long decrypt(long enc, long key) {
    int l = (int) (enc);
    int r = (int) (enc >>> 32);

    int keyPart1 = (int) (key);
    int keyPart2 = (int) (key >>> 32);

    for (int i = NUM_ROUNDS - 1; i >= 0; --i) {
      final int keyPart = ((i & 1) == 0) ? keyPart1 : keyPart2;
      final int keyNum = ((keyPart + l) >> ((i % 8) * 4)) & 0xF;
      assert keyNum >= 0 && keyNum < SHIFTS.length && keyNum < MASKS.length;
      final int shift = SHIFTS[keyNum];
      final int mask = MASKS[keyNum];
      final int lNext = (rol(r, shift) ^ mask) - keyPart;
      //System.out.println(String.format("[D] l=%s, lNext=%s, keyNum=%s", l, lNext, keyNum));

      r = l;
      l = lNext;
    }

    return (long) (l) | (((long) r) << 32);
  }
}
