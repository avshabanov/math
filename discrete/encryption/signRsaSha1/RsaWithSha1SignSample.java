import javax.crypto.Cipher;
import javax.xml.bind.DatatypeConverter;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.security.*;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.PKCS8EncodedKeySpec;
import java.security.spec.X509EncodedKeySpec;

/**
 * Demoes working with RSA by using standard java.
 *
 * Sample output:
 * <pre>
 * Keys decoded: format(publicKey)=X.509, format(privateKey)=PKCS#8
 * Message 'Hello, world!' signed: M5/v6tCFWFcWxbNinVCCeWBnu2v6XS125TqcKNeNYCuH/gm8HNQTBUP/TBrzJYTfZH27m1Fzlw3rUmBh9LDIwwios/pjZ9HQjeVg3EeAuX0H9n4qlusK+KpO2HZnRCg8kadtmU1oZpvkahnJzDZTTXoJaP/Ujn6Qt40nPFJGMDA=
 * Signature verification result=true
 * Message 'Hello, world!!' signed: X+MRQxh0nBI56x+nsMukRgitkgZL/zp/F4j6iHuAsoMH2xASx0rJk6z6/vXTwLwBPoB0KVuZjty/+kOwomUiDR1LkpYpdSHoAhlyMijP1Rx870ljhl8vaG3U2H+HkClNKRdo27pMZGISMHc3Ho6Pi4Rtue94kSt6S92tCaM9tBM=
 * Signature verification result=true
 * Message 'aa1' signed: DGPV35WN49KDt66KPDP2DCKE+AHProwqn/0rjrgllYihcfZuyJW8ogR32Q0nwlcDVIeFJN3gsoxam5xvshtULbLAjWoKCFXgdtTYuD0vWINshYRavA4JzY1EcpqOOckqcSkQI5tjPmPZGPEioUCjAofzToy94IAlpDysOkvu/ew=
 * Signature verification result=true
 * Message 'aa2' signed: JBOveEa+5uvqpyrQ+vNCh5Yw/+9RuWxnOrfuWHJAv78BWygvtRjf0Qsxcinlxzf3ZCRToN7/o5GULEVvYCmO1M5l2mST5JiuDtCTg3mWZLIJtL3r3du8gm9+YbWVYVy+KPHDWWOW3HOMur5QEC76DrNWCspBy5CcrLjWFw5adxA=
 * Signature verification result=true
 * Message 'Hello1' encrypted: A4wZfaz0TkmnzzEGTTU4fP0zDIXzKhp6mgCsg2T0DZOEfYFrFLNYZOpT5qst7rAhgcm47T0G085M7eC5tzA3L0VN2AuGRSmEbu7j5eU0JeYWnJRcRMDbzEQ+l7SarhqpJY6k4y4sLlrXGF3jdT2Bg5QBqNgSGhvxP4nbaDC2zV0=
 * Decrypted: Hello1
 * Message 'Hello2' encrypted: AEaag83lR70kJkOs1Iz4fPV3Uert2HoJV0pGD/tF4CrteZ6nD/koEbXgrj5/ZixchYHu3g8IEl6FN/E5nsvAFHR1h29w9wy8w9ipkOtwnW0VGWL02mpqbD38+OypyejsVh7UT5Dkekye6f+0NIP360ujd+Hugvod4BpXSxTXpzU=
 * Decrypted: Hello2
 * Message 'Lorem ipsum dolorem sit amet' encrypted: fCKH9t9+5DndBZlysKHZD2muvSfoo4cU2GG1s9qzR1X3gVe4r3wNEfiqMfjiF2ovrIsv01XcyIvDOJ1fPV0xOd2V6YmtgILVricDYJx2GMeqTaxAJPY4aBQVuAjonVW2M9jFrNLDHs985/XEnmi8RpEPMyms4Kef1zqqQaFKqn8=
 * Decrypted: Lorem ipsum dolorem sit amet
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class RsaWithSha1SignSample {

  // private signing key (note, that 1024 is too small by modern standards, 2048 bit key length is a standard one)
  // openssl genrsa -out private-key.pem 1024
  // openssl pkcs8 -topk8 -nocrypt -in private-key.pem -out private-key-pkcs8.pem
  // (private-key-pkcs8.pem is given here)
  private static final String SAMPLE_PEM_KEY_PRIVATE = "-----BEGIN PRIVATE KEY-----\n" +
      "MIICeAIBADANBgkqhkiG9w0BAQEFAASCAmIwggJeAgEAAoGBAMplHc62yuRVHaIe\n" +
      "XgTG20hw9eBd/sX3bWCKqOOODh1mUBk1CTJ7nkUg7/9uxLLcJzgHYV5BqWNbcV82\n" +
      "KmsPWswtZggdsNAZwhykgHD3T+hhpgSD93JexLgzyfCXt+dFdfX9A6I37TY51wLy\n" +
      "DoaUHnx2rQ4Gbp+J3ASlfmqAYE3VAgMBAAECgYA/bsmUy/1y6qpK8TGOVbTMU3r8\n" +
      "QvlimlWReGPOTetmk3ZvMAwd4liMWfJeIB1N4Wn5SXbez72DAlnZ+WP6Aen2nQkz\n" +
      "I8ZD7SwEPvdDLJ3aDQTFVseb1zBiWScYKfpKgmo+8RM/cvseBPYOtZ3nYVHgCVIa\n" +
      "omPHgv7oLuNrhrC50QJBAPRdtlv7xBIOmq7uoeLlna1KGhljQzHkzQ1r92wsQoOc\n" +
      "28NsGrO4zhz3Jc/Hp1gevAN1HuPFYnGtH2JX9/8I/3cCQQDUB95VKFzmcwdhjzCY\n" +
      "dyu1nr2NqgmZs/pi0mpsxhD7OHTEqDlRUls/3vh1OeXGYMApNWRivkDZSYcdnXfp\n" +
      "u2gTAkEAgwDSSJG6VWva5TktNHSgiUwWndGnLlJY0380D5vStLgc4LFNx1elt8WP\n" +
      "UcrZHdasOLZLLxScaBDFqHU8kE8ElQJBANLh2JHeCTfzJF416mFZ9ZE4BtOFUPMc\n" +
      "fGYZXVw+StlyN0D5B7kILlWCUJ9XLF94DudtgSBslVcHuGkOGxvPFx0CQQC2zx1R\n" +
      "LTdV6byT7PQOQ+xoHb0EngjKbeTqma66U+YXJW5r6Q8xCliC3xdiqrN+KPrMkhs2\n" +
      "9i4HXWnhSpxCSj0a\n" +
      "-----END PRIVATE KEY-----";

  // corresponds to private key above
  // openssl rsa -in private-key.pem -pubout -outform PEM -out public-key.pem
  private static final String SAMPLE_PEM_KEY_PUBLIC = "-----BEGIN PUBLIC KEY-----\n" +
      "MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQDKZR3OtsrkVR2iHl4ExttIcPXg\n" +
      "Xf7F921giqjjjg4dZlAZNQkye55FIO//bsSy3Cc4B2FeQaljW3FfNiprD1rMLWYI\n" +
      "HbDQGcIcpIBw90/oYaYEg/dyXsS4M8nwl7fnRXX1/QOiN+02OdcC8g6GlB58dq0O\n" +
      "Bm6fidwEpX5qgGBN1QIDAQAB\n" +
      "-----END PUBLIC KEY-----";

  public static void main(String[] args) throws Exception {
    final PrivateKey privateKey = decodePrivateRsaKey(SAMPLE_PEM_KEY_PRIVATE);
    final PublicKey publicKey = decodePublicRsaKey(SAMPLE_PEM_KEY_PUBLIC);
    System.out.println("Keys decoded: format(publicKey)=" + publicKey.getFormat() +
        ", format(privateKey)=" + privateKey.getFormat());

    demoSign(privateKey, publicKey, "Hello, world!");
    demoSign(privateKey, publicKey, "Hello, world!!");
    demoSign(privateKey, publicKey, "aa1");
    demoSign(privateKey, publicKey, "aa2");

    demoEncDec(privateKey, publicKey, "Hello1");
    demoEncDec(privateKey, publicKey, "Hello2");
    demoEncDec(privateKey, publicKey, "Lorem ipsum dolorem sit amet");
  }

  private static void demoSign(PrivateKey privateKey, PublicKey publicKey, String message)
      throws UnsupportedEncodingException, NoSuchAlgorithmException, InvalidKeyException, SignatureException {
    final String signature = sign(privateKey, message);
    System.out.println("Message '" + message + "' signed: " + signature);
    System.out.println("Signature verification result=" + verify(publicKey, message, signature));
  }

  private static void demoEncDec(PrivateKey privateKey, PublicKey publicKey, String message)
      throws IOException, GeneralSecurityException {
    final String cypherText = encrypt(message, publicKey);
    System.out.println("Message '" + message + "' encrypted: " + cypherText);
    System.out.println("Decrypted: " + decrypt(cypherText, privateKey));
  }

  private static byte[] decodePemContents(Reader pemReader) throws IOException {
    final StringBuilder base64Key = new StringBuilder(1024);
    try (final BufferedReader br = new BufferedReader(pemReader)) {
      String line;
      for (;;) {
        line = br.readLine();
        if (line == null) {
          throw new IOException("Malformed PEM file: missing begin directive");
        }
        if (line.startsWith("-----BEGIN")) {
          break;
        }
      }

      for (;;) {
        line = br.readLine();
        if (line == null) {
          throw new IOException("Malformed PEM file: premature end of file");
        }

        if (line.startsWith("-----END")) {
          break;
        }

        base64Key.append(line.trim());
      }
    }

    return DatatypeConverter.parseBase64Binary(base64Key.toString());
  }

  private static PrivateKey decodePrivateRsaKey(String pem)
      throws IOException, NoSuchAlgorithmException, InvalidKeySpecException {
    try (final StringReader reader = new StringReader(pem)) {
      final byte[] key = decodePemContents(reader);
      final KeyFactory keyFactory = KeyFactory.getInstance("RSA");
      final PKCS8EncodedKeySpec keySpec = new PKCS8EncodedKeySpec(key);
      return keyFactory.generatePrivate(keySpec);
    }
  }

  private static PublicKey decodePublicRsaKey(String pem)
      throws IOException, NoSuchAlgorithmException, InvalidKeySpecException {
    try (final StringReader reader = new StringReader(pem)) {
      final byte[] key = decodePemContents(reader);
      final KeyFactory keyFactory = KeyFactory.getInstance("RSA");
      final X509EncodedKeySpec keySpec = new X509EncodedKeySpec(key);
      return keyFactory.generatePublic(keySpec);
    }
  }

  private static final String SIGN_ALG_SHA1_WITH_RSA = "SHA1withRSA";

  private static String sign(PrivateKey privateKey, String message) throws NoSuchAlgorithmException, InvalidKeyException, SignatureException, UnsupportedEncodingException {
    final Signature signature = Signature.getInstance(SIGN_ALG_SHA1_WITH_RSA);
    signature.initSign(privateKey);
    signature.update(message.getBytes(StandardCharsets.UTF_8));
    return DatatypeConverter.printBase64Binary(signature.sign());
  }


  public static boolean verify(PublicKey publicKey, String message, String sign) throws SignatureException, NoSuchAlgorithmException, UnsupportedEncodingException, InvalidKeyException {
    final Signature signature = Signature.getInstance(SIGN_ALG_SHA1_WITH_RSA);
    signature.initVerify(publicKey);
    signature.update(message.getBytes(StandardCharsets.UTF_8));
    return signature.verify(DatatypeConverter.parseBase64Binary(sign));
  }

  public static String encrypt(String rawText, PublicKey publicKey) throws IOException, GeneralSecurityException {
    final Cipher cipher = Cipher.getInstance("RSA");
    cipher.init(Cipher.ENCRYPT_MODE, publicKey);
    return DatatypeConverter.printBase64Binary(cipher.doFinal(rawText.getBytes(StandardCharsets.UTF_8)));
  }

  public static String decrypt(String cipherText, PrivateKey privateKey) throws IOException, GeneralSecurityException {
    Cipher cipher = Cipher.getInstance("RSA");
    cipher.init(Cipher.DECRYPT_MODE, privateKey);
    return new String(cipher.doFinal(DatatypeConverter.parseBase64Binary(cipherText)), StandardCharsets.UTF_8);
  }
}
