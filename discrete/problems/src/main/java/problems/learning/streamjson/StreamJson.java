package problems.learning.streamjson;

import com.fasterxml.jackson.core.JsonEncoding;
import com.fasterxml.jackson.core.JsonFactory;
import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.databind.ObjectWriter;
import com.fasterxml.jackson.databind.SerializationFeature;
import lombok.val;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;

/**
 * Json streaming sample
 */
public class StreamJson {

  public static final class Demo1 {
    public static void main(String[] args) throws IOException {
      final byte[] output;

      val jsonFactory = new JsonFactory();
      try (val os = new ByteArrayOutputStream()) {
        final JsonGenerator jsonGen = jsonFactory.createGenerator(os, JsonEncoding.UTF8);
        jsonGen.useDefaultPrettyPrinter();

        writeDemoObject(jsonGen);

        jsonGen.close();

        output = os.toByteArray();
      }
      System.out.printf("Written:\n%s\n", new String(output, StandardCharsets.UTF_8));
    }

    private static void writeDemoObject(JsonGenerator jsonGen) throws IOException {
      jsonGen.writeStartObject();
      jsonGen.writeStringField("id", "i1001");
      jsonGen.writeNumberField("modification-time", 154000000);

      jsonGen.writeFieldName("role");
      jsonGen.writeStartObject();
      jsonGen.writeStringField("name", "ROLE_ADMIN");
      jsonGen.writeFieldName("flags");
      jsonGen.writeStartArray();
      jsonGen.writeNumber(128);
      jsonGen.writeNumber(42);
      jsonGen.writeNumber(317);
      jsonGen.writeEndArray();
      jsonGen.writeEndObject();

      jsonGen.writeEndObject();
      jsonGen.close();
    }
  }
}
