import javax.crypto.Mac;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.bind.DatatypeConverter;
import java.nio.charset.StandardCharsets;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;

/**
 * <pre>
 * Hex: F42BB0EEB018EBBD4597AE7213711EC60760843F, Base64: 9Cuw7rAY671Fl65yE3EexgdghD8=  <-  sign()
 * Hex: 369E2959EB49450338B212748F77D8DED74847BB, Base64: Np4pWetJRQM4shJ0j3fY3tdIR7s=  <-  sign(text)
 * Hex: DE7C9B85B8B78AA6BC8A7A36F70A90701C9DB4D9, Base64: 3nybhbi3iqa8ino29wqQcBydtNk=  <-  sign(The quick brown fox jumps over the lazy dog)
 * Hex: 0DB21F05052F323E714EF9BF1F7B000FFE97E8A0, Base64: DbIfBQUvMj5xTvm/H3sAD/6X6KA=  <-  sign(a)
 * Hex: 4512AB8F09D8667EAD11069AB4D6D4473FCBDDDB, Base64: RRKrjwnYZn6tEQaatNbURz/L3ds=  <-  sign(b)
 * Hex: D954A04E81BBC5064A707A6512B141607D8A71A8, Base64: 2VSgToG7xQZKcHplErFBYH2Kcag=  <-  sign(aa)
 * Hex: 62682D5EEDC247D2E84522ADE9A567BF4CD19CAC, Base64: YmgtXu3CR9LoRSKt6aVnv0zRnKw=  <-  sign(sample0)
 * Hex: 3C32A0BB42979421C753BEB975A199A531EEF2CE, Base64: PDKgu0KXlCHHU765daGZpTHu8s4=  <-  sign(sample1)
 * Hex: 877496BE02B3967CA70C039D900F119BAC04FB2F, Base64: h3SWvgKzlnynDAOdkA8Rm6wE+y8=  <-  sign(sample2)
 * Hex: 6549737692B540CFD13F7F1430161010FAF1A613, Base64: ZUlzdpK1QM/RP38UMBYQEPrxphM=  <-  sign(aaaaaaaaaaaaaaaaaaaaaaaaa3aaaaaaaaaa)
 * Hex: C8DF16FF33E7940F7BB7D82F19D4638ECA90C234, Base64: yN8W/zPnlA97t9gvGdRjjsqQwjQ=  <-  sign(aaaaaaaaaaaaaaaaaaaaaaaaa4aaaaaaaaaa)
 * Hex: 777B0FCCF8F2F40F3E8373486BFA6A6630B706FD, Base64: d3sPzPjy9A8+g3NIa/pqZjC3Bv0=  <-  sign(aaaaaaaaaaaaaaaaaaaaaaaaa5aaaaaaaaaa)
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class HmacSample {

  public static void main(String[] args) throws Exception {
    demo1();
  }

  private static void demo1() throws NoSuchAlgorithmException {
    final Signer signer = new Signer("key".getBytes(StandardCharsets.UTF_8));

    signAndPrint(signer, "");
    signAndPrint(signer, "text");
    signAndPrint(signer, "The quick brown fox jumps over the lazy dog");
    signAndPrint(signer, "a");
    signAndPrint(signer, "b");
    signAndPrint(signer, "aa");
    signAndPrint(signer, "sample0");
    signAndPrint(signer, "sample1");
    signAndPrint(signer, "sample2");
    signAndPrint(signer, "aaaaaaaaaaaaaaaaaaaaaaaaa3aaaaaaaaaa");
    signAndPrint(signer, "aaaaaaaaaaaaaaaaaaaaaaaaa4aaaaaaaaaa");
    signAndPrint(signer, "aaaaaaaaaaaaaaaaaaaaaaaaa5aaaaaaaaaa");
  }

  private static void signAndPrint(Signer signer, String text) {
    final byte[] sign = signer.sign(text.getBytes(StandardCharsets.UTF_8));
    System.out.println("Hex: " + DatatypeConverter.printHexBinary(sign) +
        ", Base64: " + DatatypeConverter.printBase64Binary(sign) +
        "  <-  sign(" + text + ")");
  }

  static final String SIGNING_ALG_HMAC_SHA1 = "HmacSHA1";

  // Private - sign message
  static final class Signer {
    final SecretKeySpec secretKey;
    final Mac macPrototype;

    Signer(byte[] signKey) throws NoSuchAlgorithmException {
      this.secretKey = new SecretKeySpec(signKey, SIGNING_ALG_HMAC_SHA1);
      this.macPrototype = Mac.getInstance(SIGNING_ALG_HMAC_SHA1);
    }

    public byte[] sign(byte[] text) {
      try {
        final Mac mac = (Mac) macPrototype.clone();
        mac.init(secretKey);
        return mac.doFinal(text);
      } catch (CloneNotSupportedException | InvalidKeyException e) {
        throw new IllegalStateException(e);
      }
    }
  }
}
