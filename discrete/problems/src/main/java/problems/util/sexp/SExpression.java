package problems.util.sexp;

import lombok.AllArgsConstructor;
import lombok.NonNull;
import lombok.Value;
import lombok.experimental.UtilityClass;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BiFunction;

/**
 * Simple S-expression model.
 */
@UtilityClass
public class SExpression {

  public interface Node {

    default boolean isCons() {
      return false;
    }

    default Node getCar() {
      return NIL;
    }

    default Node getCdr() {
      return NIL;
    }
  }

  public static final Node NIL = new Node() {
    @Override
    public String toString() {
      return "nil";
    }
  };

  public static final Node T = new Node() {
    @Override
    public String toString() {
      return "t";
    }
  };

  @Value(staticConstructor = "of")
  public static final class Cons implements Node {
    private final Node car;
    private final Node cdr;

    @Override public boolean isCons() {
      return true;
    }

    public void appendTo(StringBuilder sb) {
      sb.append(car.toString());
      for (Node it = cdr; it != NIL; it = it.getCdr()) {
        sb.append(' ');
        if (!it.isCons()) {
          sb.append('.').append(' ').append(it.toString());
          break;
        }

        sb.append(it.getCar().toString());
      }
    }

    @Override public String toString() {
      final StringBuilder sb = new StringBuilder(10);
      sb.append('(');
      appendTo(sb);
      sb.append(')');
      return sb.toString();
    }
  }

  @AllArgsConstructor
  public static final class Sym implements Node {
    private final String name;
    private static final Map<String, Sym> CACHE = new ConcurrentHashMap<>();

    public static Sym of(String name) {
      return CACHE.computeIfAbsent(name, Sym::new);
    }

    @Override
    public String toString() {
      return name;
    }
  }

  public static final class Immediate implements Node {
    private final Object value;

    public Object getValue() {
      return value;
    }

    private Immediate(Object value) {
      this.value = value;
    }

    public static Immediate of(Object value) {
      if (value instanceof String || value instanceof Number || value instanceof Character) {
        return new Immediate(value);
      }

      throw new UnsupportedOperationException("unsupported value=" + value);
    }

    @Override
    public String toString() {
      if (value instanceof String) {
        return '\"' + value.toString() + '\"';
      }

      if (value instanceof Character) {
        return '\'' + value.toString() + '\'';
      }

      return value.toString();
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof Immediate)) return false;

      Immediate immediate = (Immediate) o;

      return getValue() != null ? getValue().equals(immediate.getValue()) : immediate.getValue() == null;
    }

    @Override
    public int hashCode() {
      return getValue() != null ? getValue().hashCode() : 0;
    }
  }

  public static Sym sym(String s) {
    return Sym.of(s);
  }

  public static Immediate imm(double value) {
    return Immediate.of(value);
  }

  public static Cons cons(Node car, Node cdr) {
    return new Cons(car, cdr);
  }

  public static Node list(Node... nodes) {
    Node result = NIL;
    for (int i = nodes.length - 1; i >= 0; --i) {
      result = new Cons(nodes[i], result);
    }
    return result;
  }

  public static int length(Node node) {
    if (node.isCons()) {
      final Node cdr = node.getCdr();
      if (cdr == NIL) {
        return 1;
      }
      if (!cdr.isCons()) {
        throw new IllegalArgumentException("The value " + cdr + " is not a list");
      }

      return 1 + length(cdr);
    }
    return 0;
  }

  public static Node car(Node node) {
    return node.getCar();
  }

  public static Node cdr(Node node) {
    return node.getCdr();
  }

  public static Node numberp(Node node) {
    if (node instanceof Immediate) {
      if (((Immediate) node).getValue() instanceof Number) {
        return T;
      }
    }
    return NIL;
  }

  // binary operation on the S-nodes
  public static Node biop(BiFunction<Double, Double, Double> fn, Node... args) {
    Double result = 0.0;
    for (Node n : args) {
      if (!(n instanceof Immediate)) {
        throw new RuntimeException("Can't operate two numbers - one of the arguments is not a number");
      }

      final Object maybeNumber = ((Immediate) n).getValue();
      if (!(maybeNumber instanceof Double)) {
        throw new RuntimeException("Non-double arguments are not supported");
      }

      result = fn.apply(result, (Double) maybeNumber);
    }
    return Immediate.of(result);
  }

  public static Node equalsp(Node lhs, Node rhs) {
    if (lhs == rhs) {
      return T;
    }

    if (lhs.isCons()) {
      if (!rhs.isCons()) {
        return NIL;
      }
      if (equalsp(car(lhs), car(rhs)) == T && equalsp(cdr(lhs), cdr(rhs)) == T) {
        return T;
      }

      return NIL;
    }

    return lhs.equals(rhs) ? T : NIL;
  }

  public static Node memberp(Node val, Node cons) {
    if (cons == val) {
      return T;
    }

    if (cons.isCons()) {
      if (T == equalsp(val, cons.getCar())) {
        return T;
      }

      return memberp(val, cons.getCdr());
    }

    return NIL;
  }

  public static Node parseSimple(String s) {
    final Parser p = new Parser(s);
    return p.next();
  }

  public class ReaderException extends RuntimeException {
    public ReaderException(String message) {
      super(message);
    }
  }

  final class ParserException extends RuntimeException {
    public ParserException(String message) { super(message); }
  }

  final class Parser {
    private final CharSequence buffer;
    private int start;
    private int end;

    Parser(@NonNull CharSequence buffer, int start, int end) {
      this.buffer = buffer;
      this.start = start;
      this.end = end;
    }

    Parser(@NonNull CharSequence buffer) {
      this(buffer, 0, buffer.length());
    }

    private interface Special extends Node {
    }

    private static final Special OPEN_BRACE = new Special() {
      @Override
      public String toString() {
        return "Special#OPEN_BRACE";
      }
    };

    private static final Special CLOSE_BRACE = new Special() {
      @Override
      public String toString() {
        return "Special#OPEN_BRACE";
      }
    };

    public Node next() {
      Node n = nextInternal();
      if (!(n instanceof Special)) {
        return n;
      }

      if (n == CLOSE_BRACE) {
        throw new ReaderException("Premature close brace");
      }

      if (n == OPEN_BRACE) {
        return nextCons();
      }

      throw new ReaderException("Internal error: unknown special symbol=" + n);
    }

    public Node nextCons() {
      final List<Node> innerNodes = new ArrayList<>();
      for (Node n = nextInternal(); n != CLOSE_BRACE; n = nextInternal()) {
        if (n == OPEN_BRACE) {
          // read inner cons element
          n = nextCons();
        }

        // TODO: support dotted notation

        innerNodes.add(n);
      }

      if (innerNodes.isEmpty()) {
        return NIL;
      }

      return list(innerNodes.toArray(new Node[0]));
    }

    public Node nextInternal() {
      for (; start < end; ++start) { // skip whitespace
        char ch = buffer.charAt(start);
        if (ch > ' ') {
          break;
        }
      }

      int tokenStart = start;
      for (; start < end; ++start) {
        char ch = buffer.charAt(start);
        if (tokenStart == start) {
          switch (ch) { // special character?
            case '(':
              ++start;
              return OPEN_BRACE;
            case ')':
              ++start;
              return CLOSE_BRACE;
          }
        }

        if ((ch < '0' || ch > '9') && (ch < 'a' || ch > 'z') && ch != '+' && ch != '-') {
          break;
        }
      }

      if (tokenStart == start) {
        throw new ParserException("unexpected end of input or illegal character at " + tokenStart);
      }

      return toAtom(buffer.subSequence(tokenStart, start));
    }

    private Node toAtom(CharSequence val) {
      final char c0 = val.charAt(0);
      final String str = val.toString();
      if (c0 >= '0' && c0 <= '9') { return Immediate.of(Double.parseDouble(str)); } // number

      if (c0 == '\"') {
        throw new UnsupportedOperationException("TODO: parse string literals");
      }

      if (str.equals("t")) {
        return T;
      } else if (str.equals("nil")) {
        return NIL;
      }

      return Sym.of(str); // default - treat as a symbol
    }
  }
}
