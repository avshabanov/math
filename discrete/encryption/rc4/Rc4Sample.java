import javax.xml.bind.DatatypeConverter;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/**
 * RC4 demo.
 *
 * Sample output:
 * <pre>
 * Source text=abcdefj, key=a
 * encrypted=3E9C97C365BF4E
 * decrypted=abcdefj
 * Source text=bbcdefj, key=a
 * encrypted=3D95D5EBB0B83B
 * decrypted=bbcdefj
 * Source text=abcdefj, key=b
 * encrypted=6001992DA1571C
 * decrypted=abcdefj
 * Source text=bbcdefj, key=b
 * encrypted=63FB8CED1A8BEA
 * decrypted=bbcdefj
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class Rc4Sample {

  public static void main(String[] args) {
    encryptDecrypt("abcdefj", "a");
    encryptDecrypt("bbcdefj", "a");
    encryptDecrypt("abcdefj", "b");
    encryptDecrypt("bbcdefj", "b");
  }

  //
  // Private
  //

  private static void encryptDecrypt(String text, String key) {
    final byte[] buf = SimpleRC4.encrypt(text, key);
    System.out.println(String.format("Source text=%s, key=%s\nencrypted=%s\ndecrypted=%s", text, key,
        DatatypeConverter.printHexBinary(buf), SimpleRC4.decrypt(buf, key)));
  }
}

final class SimpleRC4 {
  private static final int CONTEXT_LENGTH = 256;
  private static final int KEY_SHUFFLE_COUNT = 4 * CONTEXT_LENGTH;

  private final int[] scheduledKey;

  public SimpleRC4(byte[] key) {
    this.scheduledKey = new int[CONTEXT_LENGTH];

    for (int i = 0; i < CONTEXT_LENGTH; ++i) {
      scheduledKey[i] = i;
    }

    final int shuffleCount = Math.max(KEY_SHUFFLE_COUNT, key.length);
    int j = 0;
    for (int shuffles = 0; shuffles < shuffleCount; ++shuffles) {
      final int i = shuffles % CONTEXT_LENGTH;
      j = (j + scheduledKey[i] + key[shuffles % key.length]) % CONTEXT_LENGTH;
      final int tmp = scheduledKey[i];
      scheduledKey[i] = scheduledKey[j];
      scheduledKey[j] = tmp;
    }
  }

  public static byte[] encrypt(String text, String key) {
    final SimpleRC4 rc4 = new SimpleRC4(key.getBytes(StandardCharsets.UTF_8));
    final byte[] textBytes = text.getBytes(StandardCharsets.UTF_8);
    rc4.pass(textBytes, true);
    return textBytes;
  }

  public static String decrypt(byte[] encryptedText, String key) {
    final SimpleRC4 rc4 = new SimpleRC4(key.getBytes(StandardCharsets.UTF_8));
    final byte[] textBytes = Arrays.copyOf(encryptedText, encryptedText.length);
    rc4.pass(textBytes, false);
    return new String(textBytes, StandardCharsets.UTF_8);
  }

  public void pass(byte[] text, boolean encrypt) {
    int i = 0;
    int j = 0;
    for (int pos = 0; pos < text.length; ++pos) {
      final int tmp = scheduledKey[i];
      scheduledKey[i] = scheduledKey[j];
      scheduledKey[j] = tmp;

      final int sourceByte = (int) text[pos];
      final int encryptedByte = scheduledKey[i] ^ sourceByte;
      text[pos] = (byte) encryptedByte;

      j = ((j + scheduledKey[i] + (encrypt ? encryptedByte : sourceByte)) % CONTEXT_LENGTH);
      //System.out.println("encryptedByte=" + encryptedByte + ", scheduledKey[i]=" + scheduledKey[i] + ", scheduledKey[j]=" + scheduledKey[j] + ", j=" + j);
    }
  }
}
