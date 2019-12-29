package problems.gremlin.demo.simple;

import lombok.experimental.UtilityClass;
import lombok.val;
import problems.gremlin.GremlinAdapter;
import problems.gremlin.control.Decision;
import problems.gremlin.control.SingleDecisionProvider;

import java.util.concurrent.ThreadLocalRandom;
import java.util.function.IntToLongFunction;

@UtilityClass
public class GremlinSimpleDemo {
  private static final IntToLongFunction FOO = (a) -> a + 1;

  public static final class Demo1 {
    public static void main(String[] args) {
      val wrappedFoo = GremlinAdapter.create(FOO, IntToLongFunction.class, new SingleDecisionProvider());
      val result = wrappedFoo.applyAsLong(10);
      System.out.println("result=" + result);
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      val wrappedFoo = GremlinAdapter.create(FOO, IntToLongFunction.class, (p, m, a) -> {
        if (ThreadLocalRandom.current().nextBoolean()) {
          return Decision.builder().failBefore(true).build();
        }
        return Decision.builder().build();
      });
      for (int i = 0; i < 10; ++i) {
        try {
          System.out.println("OK: result = " + wrappedFoo.applyAsLong(i));
        } catch (RuntimeException e) {
          System.out.println("FAIL");
        }
      }
    }
  }
}
