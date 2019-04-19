package problems.test.util.math;

import com.google.common.collect.ImmutableMap;
import lombok.AllArgsConstructor;
import lombok.val;
import org.junit.Test;

import java.math.BigDecimal;

import static junit.framework.Assert.*;
import static problems.util.sexp.SExpression.*;

/**
 * Tests for S-expression support.
 */
public final class SExpressionTest {

  @Test
  public void shouldComputeToString() {
    assertEquals("t", T.toString());
    assertEquals("nil", NIL.toString());
    assertEquals("1", Immediate.of(1).toString());
    assertEquals("\"a\"", Immediate.of("a").toString());
    assertEquals("(nil (t) t \"test\" a)",
        list(NIL, cons(T, NIL), T, Immediate.of("test"), Sym.of("a")).toString());
  }

  @Test
  public void shouldComputeToStringForDottedPair() {
    assertEquals("(t . t)", cons(T, T).toString());
  }

  @Test
  public void shouldComputeMemberp() {
    final Node cons = list(T, NIL, Immediate.of(1), Sym.of("a"));
    assertEquals("memberof t", T, memberp(T, cons));
    assertEquals("memberof nil", T, memberp(NIL, cons));
    assertEquals("memberof a", T, memberp(Sym.of("a"), cons));
    assertEquals("memberof 1", T, memberp(Immediate.of(1), cons));

    assertEquals("memberof 2", NIL, memberp(Immediate.of(2), cons));
  }

  @Test
  public void shouldComputeNilLength() {
    assertEquals(0, length(NIL));
  }

  @Test
  public void shouldComputeSingleListLength() {
    assertEquals(1, length(cons(Immediate.of(1), NIL)));
  }

  @Test
  public void shouldCalcNumberp() {
    assertEquals(T, numberp(Immediate.of(1)));
    assertEquals(T, numberp(Immediate.of(1.0)));
    assertEquals(T, numberp(Immediate.of(BigDecimal.valueOf(-1L))));

    assertEquals(NIL, numberp(T));
    assertEquals(NIL, numberp(NIL));
    assertEquals(NIL, numberp(Immediate.of("")));
    assertEquals(NIL, numberp(Immediate.of('a')));
    assertEquals(NIL, numberp(Sym.of("a")));
  }

  @Test
  public void shouldBeEqual() {
    val fixture = ImmutableMap.<Node, Node>builder()
        .put(NIL, NIL)
        .put(T, T)
        .put(Sym.of("a"), Sym.of("a"))
        .put(Immediate.of(1), Immediate.of(1))
        .put(Immediate.of(-10000), Immediate.of(-10000))
        .put(Immediate.of("test"), Immediate.of("test"))
        .build();

    for (val e : fixture.entrySet()) {
      val node = e.getKey();
      val expect = e.getValue();

      assertEquals(node, expect);
      assertEquals("comparing node=" + node, T, equalsp(expect, node));
    }
  }

  @Test
  public void shouldComputeHeadAndTail() {
    val fixture = ImmutableMap.<Node, ConsTestExpectations>builder()
        .put(NIL, new ConsTestExpectations(0, NIL, NIL))
        .put(cons(T, NIL), new ConsTestExpectations(1, T, NIL))
        .put(cons(T, cons(T, NIL)), new ConsTestExpectations(2, T, cons(T, NIL)))
        .build();

    for (val e : fixture.entrySet()) {
      val list = e.getKey();
      val expect = e.getValue();

      assertEquals("length for " + list, expect.length, length(list));
      assertEquals("car for " + list, expect.car, car(list));
      assertEquals("cdr for " + list, T, equalsp(expect.cdr, cdr(list)));
    }
  }

  @Test
  public void shouldParseCons() {
    assertEquals(list(T, T), parseSimple("(t t)"));
    assertEquals(list(imm(1)), parseSimple("(1)"));
    assertEquals(Sym.of("a"), parseSimple("a"));
    assertEquals(list(T, list(NIL)), parseSimple("(t (nil))"));
  }

  @Test
  public void shouldYieldCachedSymbols() {
    assertSame(Sym.of("a"), Sym.of("a"));
  }

  @AllArgsConstructor
  static final class ConsTestExpectations {
    private final int length;
    private final Node car;
    private final Node cdr;
  }
}
