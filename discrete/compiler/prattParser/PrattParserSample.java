import java.util.*;

/**
 * Variation of pratt parser, inspired by
 * http://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/
 *
 * @author Alexander Shabanov
 */
public final class PrattParserSample extends Pratt {

  public static void main(String[] args) {
    final Lexer lexer = new FeedLexer(
        new NameToken("a"),
        SimpleToken.PLUS,
        new NameToken("b"),
        SimpleToken.MUL,
        new NameToken("c"));
    final Parser parser = registerAll(new DefaultParser(lexer));

    final Expression expr = parseAll(parser);
    System.out.println("Parsed expression: " + expr);
  }

  private static Expression parseAll(Parser parser) {
    final Optional<Expression> expr = parser.parseExpression(0);
    if (!expr.isPresent()) {
      throw new ParseException("Nothing to parse");
    }
    return expr.get();
  }

  private static Parser registerAll(DefaultParser parser) {
    parser.register(SimpleToken.PLUS, new InfixOperatorParselet(1));
    parser.register(SimpleToken.MINUS, new InfixOperatorParselet(1));
    parser.register(SimpleToken.MUL, new InfixOperatorParselet(2));
    parser.register(SimpleToken.DIV, new InfixOperatorParselet(2));

    parser.register(NameToken.TYPE, new NameParselet());
    parser.register(SimpleToken.TILDE, new PrefixOperatorParselet());
    parser.register(SimpleToken.BANG, new PrefixOperatorParselet());
    return parser;
  }
}


class Pratt {

  //
  // Interfaces
  //

  interface TokenType {
  }

  interface Token {
    String getText();

    TokenType getTokenType();

    default SimpleToken expectSimpleToken() {
      throw new ParseException("Unexpected token=" + this.getTokenType());
    }
  }

  interface Lexer {
    Token next();

    Token lookAhead();
  }

  interface Expression {
  }

  interface Parser {
    Optional<Expression> parseExpression(int precedence);

    default Expression expectNextExpression() {
      final Optional<Expression> operand = this.parseExpression(0);
      if (!operand.isPresent()) {
        throw new ParseException("Abrupt end of construct");
      }
      return operand.get();
    }
  }

  interface PrefixParselet {
    Expression parse(Parser parser, Token token);
  }

  interface InfixParselet {
    Expression parse(Parser parser, Expression left, Token token);

    int getPrecedence();
  }

  static final class ParseException extends RuntimeException {
    public ParseException(String message) {
      super(message);
    }
  }

  //
  // Implementation
  //

  static abstract class AbstractComplexToken implements Token {
    static final class ComplexTokenType implements TokenType {
      private final String typeName;

      ComplexTokenType(String typeName) {
        this.typeName = typeName;
      }

      @Override
      public String toString() {
        return typeName;
      }
    }
  }

  enum SpecialToken implements Token, TokenType {
    EOF;

    @Override
    public String getText() {
      return "<EOF>";
    }

    @Override
    public TokenType getTokenType() {
      return this;
    }
  }

  static final class NameToken extends AbstractComplexToken {
    public static final TokenType TYPE = new ComplexTokenType("NAME");

    private final String text;

    public NameToken(String text) {
      this.text = Objects.requireNonNull(text, "text");
    }

    @Override
    public String getText() {
      return text;
    }

    @Override
    public TokenType getTokenType() {
      return TYPE;
    }
  }

  enum SimpleToken implements Token, TokenType {
    PLUS("+"),
    MINUS("-"),
    MUL("*"),
    DIV("/"),
    TILDE("~"),
    BANG("!");

    private final String text;

    SimpleToken(String text) {
      this.text = text;
    }

    @Override
    public String getText() {
      return text;
    }

    @Override
    public TokenType getTokenType() {
      return this;
    }

    @Override
    public SimpleToken expectSimpleToken() {
      return this;
    }
  }

  static final class NameExpression implements Expression {
    final String name;

    NameExpression(String name) {
      this.name = name;
    }

    @Override
    public String toString() {
      return name;
    }
  }

  /*static final class LiteralExpression implements Expression {
    final int num;

    public LiteralExpression(int num) {
      this.num = num;
    }

    @Override
    public String toString() {
      return String.format("%d", num);
    }
  }*/

  static final class BinaryExpression implements Expression {
    final Expression left;
    final Expression right;
    final SimpleToken op;

    public BinaryExpression(Expression left, Expression right, SimpleToken op) {
      this.left = left;
      this.right = right;
      this.op = op;
    }

    @Override
    public String toString() {
      return "(" + left.toString() + " " + op.toString() + " " + right.toString() + ")";
    }
  }

  static final class UnaryExpression implements Expression {
    final Expression expr;
    final SimpleToken op;

    public UnaryExpression(Expression expr, SimpleToken op) {
      this.expr = expr;
      this.op = op;
    }

    @Override
    public String toString() {
      return "(" + op.toString() + expr.toString() + ")";
    }
  }

  static final class FeedLexer implements Lexer {
    private final List<Token> tokens;
    private int pos;

    public FeedLexer(Token... tokens) {
      this.tokens = Collections.unmodifiableList(new ArrayList<>(Arrays.asList(tokens)));
    }

    @Override
    public Token next() {
      Token result = SpecialToken.EOF;
      if (pos < tokens.size()) {
        result = tokens.get(pos);
        ++pos;
      }
      return result;
    }

    @Override
    public Token lookAhead() {
      return pos < tokens.size() ? tokens.get(pos) : SpecialToken.EOF;
    }
  }

  static final class DefaultParser implements Parser {
    private final Map<TokenType, PrefixParselet> prefixParseletMap = new HashMap<>();
    private final Map<TokenType, InfixParselet> infixParseletMap = new HashMap<>();
    private final Lexer lexer;

    public DefaultParser(Lexer lexer) {
      this.lexer = lexer;
    }

    public void register(TokenType tokenType, PrefixParselet prefixParselet) {
      prefixParseletMap.compute(tokenType, (k, old) -> {
        if (old != null) {
          throw new IllegalStateException("Duplicate registration for token=" + tokenType);
        }
        return prefixParselet;
      });
    }

    public void register(TokenType tokenType, InfixParselet infixParselet) {
      infixParseletMap.compute(tokenType, (k, old) -> {
        if (old != null) {
          throw new IllegalStateException("Duplicate registration for token=" + tokenType);
        }
        return infixParselet;
      });
    }

    @Override
    public Optional<Expression> parseExpression(int precedence) {
      Token token = lexer.next();
      if (token == SpecialToken.EOF) {
        return Optional.empty();
      }

      final PrefixParselet prefixParselet = prefixParseletMap.get(token.getTokenType());
      if (prefixParselet == null) {
        throw new ParseException("Unknown parser construct starting with token: " + token);
      }

      final Expression left = prefixParselet.parse(this, token);

      token = lexer.lookAhead();
      final InfixParselet infixParselet = infixParseletMap.get(token.getTokenType());
      if (infixParselet == null) {
        return Optional.of(left);
      }

      final int infixParseletPrecedence = infixParselet.getPrecedence();
      if (precedence >= infixParseletPrecedence) {
        return Optional.of(left);
      }

      lexer.next(); // consume lookahead token
      return Optional.of(infixParselet.parse(this, left, token));
    }
  }

  //
  // Parselet
  //

  static final class NameParselet implements PrefixParselet {

    @Override
    public Expression parse(Parser parser, Token token) {
      return new NameExpression(token.getText());
    }
  }

  static final class PrefixOperatorParselet implements PrefixParselet {

    @Override
    public Expression parse(Parser parser, Token token) {
      final Expression operand = parser.expectNextExpression();
      return new UnaryExpression(operand, token.expectSimpleToken());
    }
  }

  static final class InfixOperatorParselet implements InfixParselet {
    private final int precedence;

    public InfixOperatorParselet(int precedence) {
      this.precedence = precedence;
    }

    @Override
    public Expression parse(Parser parser, Expression left, Token token) {
      final Optional<Expression> right = parser.parseExpression(getPrecedence());
      if (!right.isPresent()) {
        throw new ParseException("Abrupt end of expression");
      }
      return new BinaryExpression(
          left,
          right.get(),
          token.expectSimpleToken());
    }

    @Override
    public int getPrecedence() {
      return precedence;
    }
  }
}
