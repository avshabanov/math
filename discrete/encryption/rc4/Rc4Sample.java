
import javax.xml.bind.DatatypeConverter;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.concurrent.ThreadLocalRandom;

import static support.EncryptionUtils.intFromByteArray;
import static support.EncryptionUtils.longFromByteArray;
import static support.EncryptionUtils.writeInt;
import static support.EncryptionUtils.writeLong;

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

    obfuscateDeobfuscate(0);
    obfuscateDeobfuscate(1);
    obfuscateDeobfuscate(-1);
    obfuscateDeobfuscate(ThreadLocalRandom.current().nextLong());
  }

  //
  // Private
  //

  private static void encryptDecrypt(String text, String key) {
    final byte[] buf = SimpleRC4.encrypt(text, key);
    final String decryptedText = SimpleRC4.decrypt(buf, key);
    if (!text.equals(decryptedText)) {
      throw new AssertionError("Failed to decrypt text=" + text + " with key=" + key +
          " from buf=" + Arrays.toString(buf));
    }
    System.out.println(String.format("Source text=%s, key=%s\nencrypted=%s\ndecrypted=%s", text, key,
        DatatypeConverter.printHexBinary(buf), decryptedText));
  }

  private static void obfuscateDeobfuscate(long id) {
    final String token = RC4Obfuscator.obfuscate(id);
    final long newId = RC4Obfuscator.deobfuscate(token);
    if (id != newId) {
      throw new AssertionError("Obfuscation mismatch for id=" + id + ", deobfuscatedId=" + newId + ", token=" + token);
    }
    System.out.println("[OBFUSCATE] id=" + id + ", token=" + token);
  }
}

final class RC4Obfuscator {
  private RC4Obfuscator() {}

  private static final byte[] OBFUSCATE_KEY = { 12, -125, 65, -99, 7, 85, 1, 29 };
  private static final int DEFAULT_TOKEN = 0xab5bead3;
  private static final int OBFUSCATE_BUFFER_LENGTH = 12; // 8 bytes for long, 4 bytes for token

  public static String obfuscate(final long id, final int token) {
    final byte[] result = new byte[OBFUSCATE_BUFFER_LENGTH];
    final int nextOffset = writeLong(result, 0, id);
    writeInt(result, nextOffset, token);

    new SimpleRC4(OBFUSCATE_KEY).pass(result, true);
    return DatatypeConverter.printBase64Binary(result);
  }

  public static String obfuscate(long id) {
    return obfuscate(id, DEFAULT_TOKEN);
  }

  public static long deobfuscate(String str, int token) {
    final byte[] bytes = DatatypeConverter.parseBase64Binary(str);
    if (bytes.length != OBFUSCATE_BUFFER_LENGTH) {
      throw new IllegalArgumentException("Malformed obfuscated string=" + str);
    }

    new SimpleRC4(OBFUSCATE_KEY).pass(bytes, false);

    final long id = longFromByteArray(bytes, 0);
    final int resultToken = intFromByteArray(bytes, 8);
    if (resultToken != token) {
      throw new IllegalArgumentException("Invalid obfuscated string=" + str);
    }
    return id;
  }

  public static long deobfuscate(String str) {
    return deobfuscate(str, DEFAULT_TOKEN);
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
      j = (CONTEXT_LENGTH + j + scheduledKey[i] + key[shuffles % key.length]) % CONTEXT_LENGTH;
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

      j = (CONTEXT_LENGTH + j + scheduledKey[i] + (encrypt ? encryptedByte : sourceByte)) % CONTEXT_LENGTH;
      //System.out.println("encryptedByte=" + encryptedByte + ", scheduledKey[i]=" + scheduledKey[i] + ", scheduledKey[j]=" + scheduledKey[j] + ", j=" + j);
    }
  }
}
