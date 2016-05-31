import java.io.InputStream;
import java.io.OutputStream;

/**
 * Structure:
 *
 * <pre>
 * [HeaderFile]
 *    LookupTableSize, int
 *    EntryCount, int
 *    LookupTableContentSize - for compactification after deletion
 * [LookupTableContent]
 *    [LookupTableContentEntry#1]
 *        [Key]
 *        [ContentValueIndex] - index of content in the content file
 *    [LookupTableContentEntry#2]
 *    ...
 *    [LookupTableContentEntry#N]
 *
 * [ContentFile]
 *    [ContentEntry]
 *      Length, int
 *      Checksum
 *      ContentBytes
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class FileBasedHashTableExample {


  private interface ContentProvider {

    InputStream createInputStream();

    OutputStream createOutputStream();
  }

  private static final class Dht {


    public String get(String key) {
      throw new UnsupportedOperationException();
    }

    public String put(String key, String value) {
      throw new UnsupportedOperationException();
    }
  }
}
