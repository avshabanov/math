/**
 * Sample run:
 * <pre>
 * [OK] Withdrawn 0 amount of money
 * [OK] Withdrawn 1 amount of money
 * [OK] Withdrawn 2 amount of money
 * [OK] Withdrawn 3 amount of money
 * [OK] Withdrawn 4 amount of money
 * [OK] Withdrawn 5 amount of money
 * [OK] Withdrawn 15 amount of money
 * [OK] Withdrawn 17 amount of money
 * [OK] Withdrawn 1997 amount of money
 * [OK] Withdrawn 2017 amount of money
 * [OK] Withdrawn 18753 amount of money
 * [OK] Withdrawn 65534 amount of money
 * [OK] Withdrawn 65535 amount of money
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class WithdrawalsExample {

  public static void main(String[] args) {
    demo(0);
    demo(1);
    demo(2);
    demo(3);
    demo(4);
    demo(5);
    demo(15);
    demo(17);
    demo(1997);
    demo(2017);
    demo(18753);
    demo(Account.MAX_VALUE - 1);
    demo(Account.MAX_VALUE);
  }

  public static void demo(int expected) {
    final Account account = new AccountImpl(expected);
    final int withdrawn = withdrawAll(account);
    if (withdrawn != expected) {
      throw new AssertionError("withdrawn amount=" + withdrawn + " of money is not the same as expected=" + expected);
    }

    System.out.println("[OK] Withdrawn " + withdrawn + " amount of money");
  }

  public static int withdrawAll(Account account) {
    int result = 0;
    int valueToWithdraw = Account.MAX_VALUE;
    while (valueToWithdraw > 0) {
      int withdrawal = account.withdraw(valueToWithdraw);
      if (withdrawal == 0) {
        valueToWithdraw = valueToWithdraw / 2;
        continue;
      }

      result += withdrawal;
    }

    return result;
  }

  interface Account {
    int MAX_VALUE = 65535;

    int withdraw(int value);
  }

  static final class AccountImpl implements Account {
    int amount;

    public AccountImpl(int amount) {
      this.amount = amount;
    }

    @Override
    public int withdraw(int value) {
      if (value < 0 || value > MAX_VALUE) {
        throw new IllegalArgumentException();
      }

      if (value > amount) {
        return 0;
      }

      amount -= value;

      return value;
    }
  }
}
