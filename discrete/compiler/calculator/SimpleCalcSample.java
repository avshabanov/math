
/**
 * Primitive calculator sample implemented as interpreter.
 * Contains: tokenizer (lexer), parser, AST node definition and AST evaluator.
 *
 * Sample run:
 *
 * <pre>
 * Expr 2 parsed as [2] and evaluated to 2
 * Expr 2 + 3 parsed as [2 + 3] and evaluated to 5
 * Expr 1 + 3 * 2 parsed as [1 + 3 * 2] and evaluated to 7
 * Expr 1 + 2 * 3 + 4 parsed as [1 + 2 * 3 + 4] and evaluated to 11
 * </pre>
 *
 * @author Alexander Shabanov
 */
public class SimpleCalcSample {

  public static void main(String[] args) {
    demo("2");
    demo("2 + 3");
    demo("1 + 3 * 2");
    demo("1 + 2 * 3 + 4");
  }

  private static void demo(String expr) {
    final AstNode node = parse(expr);
    System.out.println("Expr " + expr + " parsed as [" + node + "] and evaluated to " + eval(node));
  }

  //
  // Evaluation
  //

  private static int eval(AstNode node) {
    return node.apply(new AstVisitor<Integer>() {
      @Override
      public Integer visitNum(Num num) {
        return num.value;
      }

      @Override
      public Integer visitOp(Op op) {
        final int left = eval(op.left);
        final int right = eval(op.right);

        switch (op.opType) {
          case ADD:
            return left + right;

          case SUB:
            return left - right;

          case MUL:
            return left * right;

          case DIV:
            return left / right;

          default:
            throw new IllegalStateException();
        }
      }
    });
  }

  //
  // Parse
  //

  private static AstNode parse(String s) {
    final TokenReader tokenReader = new StringTokenReader(s);
    tokenReader.expect(TokenType.NUMBER);
    return parseAfterNum(new Num(tokenReader.number()), tokenReader);
  }

  private static AstNode parseAfterNum(AstNode left, TokenReader tokenReader) {
    tokenReader.next();
    final TokenType tokenType = tokenReader.getCurrentTokenType();

    if (tokenType == TokenType.EOF) {
      return left;
    }

    if (tokenType != TokenType.OPERATION) {
      throw new IllegalArgumentException("Invalid expression");
    }

    final OpType opType = tokenReader.opType();

    // right expression should always be a number
    tokenReader.expect(TokenType.NUMBER);
    final AstNode right = new Num(tokenReader.number());

    if (opType == OpType.MUL || opType == OpType.DIV) {
      final AstNode nextLeft = new Op(opType, left, right);
      return parseAfterNum(nextLeft, tokenReader);
    }

    return new Op(opType, left, parseAfterNum(right, tokenReader));
  }

  //
  // AST
  //

  private interface AstVisitor<R> {
    R visitNum(Num num);
    R visitOp(Op op);
  }

  private interface AstNode {
    <R> R apply(AstVisitor<R> visitor);
  }

  private static final class Num implements AstNode {
    final int value;

    public Num(int value) {
      this.value = value;
    }

    @Override
    public <R> R apply(AstVisitor<R> visitor) {
      return visitor.visitNum(this);
    }

    @Override
    public String toString() {
      return Integer.toString(value);
    }
  }

  private static final class Op implements AstNode {
    final OpType opType;
    final AstNode left;
    final AstNode right;

    public Op(OpType opType, AstNode left, AstNode right) {
      this.opType = opType;
      this.left = left;
      this.right = right;
    }

    @Override
    public <R> R apply(AstVisitor<R> visitor) {
      return visitor.visitOp(this);
    }

    @Override
    public String toString() {
      return left.toString() + ' ' + opType.getText() + ' ' + right;
    }
  }

  private enum OpType {
    ADD('+'),
    SUB('-'),
    MUL('*'),
    DIV('/');

    final char text;

    OpType(char text) {
      this.text = text;
    }

    public char getText() {
      return text;
    }
  }

  //
  // Reader
  //

  private enum TokenType {
    NUMBER,
    OPERATION,
    EOF,
    ERROR
  }

  private interface TokenReader {
    void next();

    TokenType getCurrentTokenType();

    default void expect(TokenType tokenType) {
      next();
      if (getCurrentTokenType() != tokenType) {
        throw new IllegalArgumentException("Token expected=" + tokenType + ", got=" + getCurrentTokenType());
      }
    }

    int number();
    OpType opType();
  }

  private static final class StringTokenReader implements TokenReader {
    private final String text;
    private int index;
    private OpType opType;
    private int number;
    private TokenType tokenType = TokenType.ERROR;

    public StringTokenReader(String text) {
      this.text = text;
    }

    @Override
    public void next() {
      for (; index < text.length();) {
        char ch = text.charAt(index);

        if (ch == ' ') {
          ++index;
          continue;
        }

        int startNumIndex = index;
        while (ch >= '0' && ch <= '9') {
          ++index;
          if (index == text.length()) {
            break;
          }
          ch = text.charAt(index);
        }

        if (index > startNumIndex) {
          this.tokenType = TokenType.NUMBER;
          this.number = Integer.parseInt(text.substring(startNumIndex, index));
          return;
        }

        final OpType opType = opTypeFromChar(ch);
        if (opType != null) {
          ++index;
          this.tokenType = TokenType.OPERATION;
          this.opType = opType;
          return;
        }

        // unexpected token
        this.tokenType = TokenType.ERROR;
        ++index;
        return;
      }

      this.tokenType = TokenType.EOF;
    }

    @Override
    public TokenType getCurrentTokenType() {
      if (tokenType == null) {
        throw new IllegalStateException();
      }
      return tokenType;
    }

    @Override
    public int number() {
      if (getCurrentTokenType() != TokenType.NUMBER) {
        throw new IllegalStateException();
      }
      return number;
    }

    @Override
    public OpType opType() {
      if (getCurrentTokenType() != TokenType.OPERATION) {
        throw new IllegalStateException();
      }
      return opType;
    }

    //
    // Private
    //

    private static OpType opTypeFromChar(char ch) {
      switch (ch) {
        case '+':
          return OpType.ADD;

        case '-':
          return OpType.SUB;

        case '/':
          return OpType.DIV;

        case '*':
          return OpType.MUL;
      }
      return null;
    }
  }
}
