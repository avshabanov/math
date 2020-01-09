package problems.leet100.coinChange;

import java.util.Arrays;

/**
 * TBD
 */
public class CoinChangeSolution {

  public static void main(String[] args) {
    demo(11, 1, 3);
    demo(11, 2, 5);
    demo(7, 1);
    demo(19, 5, 7);
  }

  private static void demo(int sum, int... coins) {
    final int minChangeQuantity = coinChange(coins, sum);
    System.out.printf(
        "For coins=%s and sum=%d minimum coin amount is %d coin(s)\n",
        Arrays.toString(coins),
        sum,
        minChangeQuantity
    );
  }

  private static int coinChange(int[] coins, int amount) {
    if (amount == 0) {
      return 0;
    }

    final int[] quantities = new int[amount + 1];
    for (final int coin : coins) {
      if (coin <= 0 || coin > amount) {
        continue;
      }

      if (coin == amount) {
        return 1; // 1 coin matches this sum
      }

      // try all possible combinations for this coin
      for (int quantity = 1;; ++quantity) {
        final int coinSum = quantity * coin;
        if (coinSum > amount) {
          break;
        }
        final int currentQuantity = quantities[coinSum];
        quantities[coinSum] = currentQuantity > 0 ? Math.min(currentQuantity, quantity) : quantity;

        // fill all the complement amounts with the previously found coin combinations
        // start from the end to avoid duplicate search attempts
        final int precedingAmountThreshold = amount - coinSum;
        for (int predSum = precedingAmountThreshold; predSum >= 1; --predSum) {
          final int predQuantity = quantities[predSum];
          if (predQuantity == 0) {
            continue;
          }

          final int derivedAmount = predSum + coinSum;
          final int oldQuantity = quantities[derivedAmount];
          final int newQuantity = quantity + predQuantity;
          quantities[derivedAmount] = oldQuantity > 0 ? Math.min(oldQuantity, newQuantity) : newQuantity;
        }
      }
    }

    final int result = quantities[amount];
    return result == 0 ? -1 : result;
  }
}
