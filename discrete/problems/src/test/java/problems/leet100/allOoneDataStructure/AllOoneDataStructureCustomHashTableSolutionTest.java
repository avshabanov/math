package problems.leet100.allOoneDataStructure;

import org.junit.Test;

import java.util.Random;

import static org.junit.Assert.assertEquals;
import static problems.leet100.allOoneDataStructure.AllOoneDataStructureCustomHashTableSolution.AllOne;

public class AllOoneDataStructureCustomHashTableSolutionTest {

  @Test
  public void shouldReturnNothingForEmptyMap() {
    final AllOne ao = new AllOne();
    assertEquals("", ao.getMaxKey());
    assertEquals("", ao.getMinKey());

    ao.dec("1");
    assertEquals("", ao.getMaxKey());
    assertEquals("", ao.getMinKey());
  }

  @Test
  public void shouldMatchMaxAndMinForSingleOperation() {
    final String key = "1";
    final AllOne ao = new AllOne();

    ao.inc(key);
    assertEquals("min key addition", "1", ao.getMaxKey());
    assertEquals("max key addition", "1", ao.getMinKey());

    ao.dec(key);
    assertEquals("max key after removal", "", ao.getMaxKey());
    assertEquals("min key after removal", "", ao.getMinKey());
  }

  @Test
  public void shouldGraduallyIncreaseMax() {
    final AllOne ao = new AllOne();

    inc(ao, "3", "3", "2");
    assertEquals("[3x2+2x1] min key", "2", ao.getMinKey());
    assertEquals("[3x2+2x1] max key", "3", ao.getMaxKey());

    inc(ao, "2", "2");
    assertEquals("[3x2+2x3] min key", "3", ao.getMinKey());
    assertEquals("[3x2+2x3] max key", "2", ao.getMaxKey());

    inc(ao, "3", "3", "1");

    // expected state: four '3', three '2', one '1'
    assertEquals("[all] min key", "1", ao.getMinKey());
    assertEquals("[all] max key", "3", ao.getMaxKey());
  }

  @Test
  public void shouldGraduallyDecreaseMax() {
    final AllOne ao = new AllOne();

    inc(ao, "3", "3", "3", "3", "2", "2", "2", "1");
    dec(ao, "3", "3");

    assertEquals("[...-3x2] min key", "1", ao.getMinKey());
    assertEquals("[...-3x2] max key", "2", ao.getMaxKey());

    dec(ao, "2", "2", "2");
    assertEquals("[...-2x3] min key", "1", ao.getMinKey());
    assertEquals("[...-2x3] max key", "3", ao.getMaxKey());

    dec(ao, "3", "3");
    assertEquals("[...-3x2 (2)] min key", "1", ao.getMinKey());
    assertEquals("[...-3x2 (2)] max key", "1", ao.getMaxKey());

    dec(ao, "1");
    assertEquals("[...-1] min key", "", ao.getMinKey());
    assertEquals("[...-1] max key", "", ao.getMaxKey());
  }

  @Test
  public void shouldAdjustAfterResizes() {
    final Random random = new Random(1234);
    for (int count = 3; count < 20; ++count) {
      final int[] arr = new int[count * (count + 1) / 2];
      for (int i = 0, k = 0; i < count; ++i) {
        final int num = i + 1;
        for (int j = 0; j < num; ++j) {
          arr[k++] = num;
        }
      }

      shuffleInts(arr, random);
      final AllOne ao = new AllOne();
      for (int elem : arr) {
        ao.inc(Integer.toString(elem));
      }

      assertEquals("after insert (min); count=" + count, "1", ao.getMinKey());
      assertEquals("after insert (max); count=" + count, Integer.toString(count), ao.getMaxKey());

      shuffleInts(arr, random);
      for (int elem : arr) {
        ao.dec(Integer.toString(elem));
      }

      assertEquals("after decrement (min); count=" + count, "", ao.getMinKey());
      assertEquals("after decrement (max); count=" + count, "", ao.getMaxKey());
    }
  }

  private static void inc(AllOne ao, String... keys) {
    for (final String key : keys) {
      ao.inc(key);
    }
  }

  private static void dec(AllOne ao, String... keys) {
    for (final String key : keys) {
      ao.dec(key);
    }
  }

  private static void shuffleInts(int[] arr, Random random) {
    for (int i = arr.length; i > 1; --i) {
      final int leftPos = i - 1;
      final int rightPos = random.nextInt(i);
      if (leftPos == rightPos) {
        continue;
      }

      final int left = arr[leftPos];
      arr[leftPos] = arr[rightPos];
      arr[rightPos] = left;
    }
  }
}
