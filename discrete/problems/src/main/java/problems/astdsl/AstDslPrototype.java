package problems.astdsl;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/**
 * AST DSL demo.
 * "...if you can write it in Java, you can write it in anything."
 */
public class AstDslPrototype {

  private static class Dsl {

    static void expr(Writer w, Object... values) {
      try {
        for (Object v : values) {
          if (v instanceof Node) {
            ((Node) v).writeTo(w);
            continue;
          }
          w.append(String.valueOf(v));
        }
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }

    static void stmt(Writer w, Node[] body, String format, Object... values) {
      try {
        if (format != null) {
          values = Arrays.stream(values).map(v -> {
            if (v instanceof Node) {
              try (final StringWriter w2 = new StringWriter()) {
                ((Node) v).writeTo(w2);
                return w2.toString();
              } catch (IOException e) {
                throw new RuntimeException(e);
              }
            }
            return String.valueOf(v);
          }).toArray();
          w.append(String.format(format, values));
        } else {
          expr(w, values);
        }

        w.append(' ').append('{');

        final Writer iw = new SimpleIndentedWriter(w);
        iw.append('\n');
        for (final Node bodyNode : body) {
          bodyNode.writeTo(iw);
        }

        w.append('}').append('\n');
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    }

    interface Node {
      void writeTo(Writer w) throws IOException;
    }

    protected Node n(Node n) {
      return n;
    }


    Node $br() { return n((w) -> expr(w, '\n')); }
    Node $lineComment(String... text) {
      return n((w) -> Arrays.stream(text).forEach(t -> expr(w, "// ", t, '\n')));
    }

    Node $args(Node... args) {
      return n((w) -> {
        w.append('(');
        for (int i = 0; i < args.length; ++i) {
          if (i > 0) {
            w.append(", ");
          }
          args[i].writeTo(w);
        }
        w.append(')');
      });
    }
    Node $op(Node lhs, String op, Node rhs) { return n((w) -> expr(w, lhs, ' ', op, ' ', rhs, ';', '\n')); }
    Node $var(Node type, Node name) { return n((w) -> expr(w, type, ' ', name, ';', '\n')); }
    Node $id(String name) { return n((w) -> expr(w, name)); }
    Node $id(Number val) { return n((w) -> expr(w, val)); }
    Node $return(Node n) { return n((w) -> expr(w, "return", ' ', n, ";\n")); }
    Node $publicMethod(Node type, Node name, Node args, Node... body) {
      return n((w) -> stmt(w, body, "public %s %s %s", type, name, args));
    }
  }

  public static final class Demo1 {
    public static void main(String[] args) throws Exception {
      final Writer out = new OutputStreamWriter(System.out, StandardCharsets.UTF_8);
      System.out.println("AST DSL demo:");

      Dsl d = new Dsl();
      d.$id("qwerty").writeTo(out);
      d.$br().writeTo(out);

      d.$return(d.$id("qwerty")).writeTo(out);
      d.$br().writeTo(out);

      out.flush();
    }
  }

  public static final class Demo2 extends Dsl {
    public static void main(String[] args) throws Exception {
      final Writer out = new OutputStreamWriter(System.out, StandardCharsets.UTF_8);

      Demo2 demo = new Demo2();
      demo.createDemoProperty().writeTo(out);
      demo.$br().writeTo(out);

      out.flush();
    }

    private final Node $int = $id("int");

    Node createDemoProperty() {
      Node $a = $id("a"), $b = $id("b");

      return $publicMethod($int, $id("getFoo"), $args($int, $a),
          $var($int, $b),
          $br(),
          $op($b, "=", $id(0)),
          $op($b, "+=", $a),
          $return($b));
    }
  }
}
