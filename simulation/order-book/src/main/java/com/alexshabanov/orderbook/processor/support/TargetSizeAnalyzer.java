package com.alexshabanov.orderbook.processor.support;

import com.alexshabanov.orderbook.model.AddBookLogEntry;
import com.alexshabanov.orderbook.model.BookLogEntry;
import com.alexshabanov.orderbook.model.ReduceBookLogEntry;
import com.alexshabanov.orderbook.model.SideKind;
import com.alexshabanov.orderbook.processor.BookLogProcessor;

import java.io.IOException;
import java.io.PrintStream;
import java.math.BigDecimal;
import java.util.*;

/**
 * Income/expense analyzer of the book order log.
 *
 * @author Alexander Shabanov
 */
public class TargetSizeAnalyzer implements BookLogProcessor {
  private final long targetSize;
  private final PrintStream out;

  private final Map<String, OrderState> orderMap;
  private List<PriceCalculator> priceCalculators;

  public TargetSizeAnalyzer(PrintStream out, long targetSize) {
    if (targetSize <= 0L) {
      throw new IllegalArgumentException("Target size expected to be a positive number");
    }

    this.targetSize = targetSize;
    this.out = Objects.requireNonNull(out, "Output stream is null");

    // create order map
    this.orderMap = new HashMap<>(1000);
    this.priceCalculators = Arrays.asList(new ExpensePriceCalculator(), new IncomePriceCalculator());
  }

  @Override
  public void process(BookLogEntry entry) {
    Objects.requireNonNull(entry, "entry");

    processEntry(entry);
    outputPriceChanges(entry);
  }

  @Override
  public void close() throws IOException {
    // clear state
    this.orderMap.clear();
    for (final PriceCalculator priceCalculator : this.priceCalculators) {
      priceCalculator.clear();
    }
  }

  //
  // Private
  //

  private void processEntry(BookLogEntry entry) {
    if (processAddEntry(entry.asAddEntry())) {
      return;
    }

    if (processReduceEntry(entry.asReduceEntry())) {
      return;
    }

    // should never happen if all the entries are properly mapped above
    throw new IllegalStateException("Unknown type of entry=" + entry);
  }

  private void outputPriceChanges(BookLogEntry entry) {
    for (final PriceCalculator priceCalculator : this.priceCalculators) {
      priceCalculator.outputDifference(entry, out, targetSize);
    }
  }

  private boolean processAddEntry(AddBookLogEntry e) {
    if (e == null) {
      return false;
    }

    final OrderState newOrder = new OrderState(e.getOrderId(), e.getPrice(), e.getSideType(), e.getSize());
    final OrderState prevOrder = this.orderMap.put(e.getOrderId(), newOrder);

    if (prevOrder != null) {
      // prevent double insertion
      throw new IllegalStateException("Order book entry expected to be added once then reduced to zero");
    }

    for (final PriceCalculator priceCalculator : this.priceCalculators) {
      priceCalculator.notifyOrderAdded(newOrder);
    }

    return true;
  }

  private boolean processReduceEntry(ReduceBookLogEntry entry) {
    if (entry == null) {
      return false;
    }

    final OrderState state = this.orderMap.get(entry.getOrderId());
    if (state == null) {
      throw new IllegalStateException("There is no order with ID=" + entry.getOrderId() + " to reduce");
    }

    final long newSize = state.size - entry.getSize();
    if (newSize <= 0L) {
      // remove order entry when its size becomes less than or equal to zero
      this.orderMap.remove(entry.getOrderId());

      for (final PriceCalculator priceCalculator : this.priceCalculators) {
        priceCalculator.notifyOrderRemoved(entry.getOrderId());
      }
    } else {
      state.size = newSize;
    }

    return true;
  }

  /**
   * Internal class that maintains order state, this state is uniquely associated with the corresponding orderId.
   */
  private static final class OrderState {
    private final String orderId;
    private final BigDecimal price;
    private final SideKind side;
    private long size;

    OrderState(String orderId, BigDecimal price, SideKind side, long size) {
      this.orderId = orderId;
      this.price = price;
      this.side = side;
      this.size = size;
    }
  }

  /**
   * Interface to internal entity that deals with price calculations (either income or expense change reports).
   */
  private interface PriceCalculator {
    void outputDifference(BookLogEntry entry, PrintStream out, long targetSize);
    void notifyOrderAdded(OrderState order);
    void notifyOrderRemoved(String orderId);
    void clear();
  }

  private static abstract class AbstractPriceCalculator implements PriceCalculator {
    final List<OrderState> orders = new ArrayList<>();
    BigDecimal previousPriceReported = null;

    @Override
    public void outputDifference(BookLogEntry entry, PrintStream out, long targetSize) {
      BigDecimal currentExpense = calcPrice(targetSize);

      if (currentExpense == null) {
        if (previousPriceReported != null) {
          out.println(String.format("%d %s NA", entry.getTimestamp(), getActionSide().getCode()));
          previousPriceReported = null;
        }

        return;
      }

      if (previousPriceReported == null || previousPriceReported.compareTo(currentExpense) != 0) {
        out.println(String.format("%d %s %s", entry.getTimestamp(), getActionSide().getCode(), currentExpense));
        previousPriceReported = currentExpense;
      }
    }

    @Override
    public void notifyOrderAdded(OrderState order) {
      if (order.side == getOpposingActionSide()) {
        // use straight insertion to avoid redundant sorting
        int pos = Collections.binarySearch(this.orders, order, getOrderStateComparator());
        if (pos < 0) {
          pos = -1 - pos;
        }

        this.orders.add(pos, order);
      }
    }

    @Override
    public void notifyOrderRemoved(String orderId) {
      this.orders.removeIf((o) -> o.orderId.equals(orderId));
    }

    @Override
    public void clear() {
      this.previousPriceReported = null;
      this.orders.clear();
    }

    BigDecimal calcPrice(long targetSize) {
      long remainingSharesToHit = targetSize;
      BigDecimal currentPrice = BigDecimal.ZERO;

      for (final OrderState order : orders) {
        final long sharesToTake = Math.min(remainingSharesToHit, order.size);
        remainingSharesToHit -= sharesToTake;
        currentPrice = currentPrice.add(order.price.multiply(BigDecimal.valueOf(sharesToTake)));

        if (remainingSharesToHit == 0L) {
          break;
        }

        assert remainingSharesToHit > 0L;
      }

      return remainingSharesToHit == 0L ? currentPrice : null;
    }

    abstract SideKind getActionSide();

    abstract SideKind getOpposingActionSide();

    abstract Comparator<OrderState> getOrderStateComparator();
  }

  /**
   * Calculates expenses from buying shares.
   */
  private static final class ExpensePriceCalculator extends AbstractPriceCalculator {

//    @Override
//    Stream<OrderState> transformOrders(Collection<OrderState> orders) {
//      return orders.stream().filter(s -> s.side == SideKind.SELL).sorted(Comparator.comparing(o -> o.price));
//    }

    @Override
    SideKind getActionSide() {
      return SideKind.BUY;
    }

    @Override
    SideKind getOpposingActionSide() {
      return SideKind.SELL;
    }

    @Override
    Comparator<OrderState> getOrderStateComparator() {
      return Comparator.comparing(o -> o.price);
    }
  }

  /**
   * Calculates income from selling shares.
   */
  private static final class IncomePriceCalculator extends AbstractPriceCalculator {

//    @Override
//    Stream<OrderState> transformOrders(Collection<OrderState> orders) {
//      return orders.stream().filter(s -> s.side == SideKind.BUY).sorted((o1, o2) -> o2.price.compareTo(o1.price));
//    }

    @Override
    SideKind getActionSide() {
      return SideKind.SELL;
    }

    @Override
    SideKind getOpposingActionSide() {
      return SideKind.BUY;
    }

    @Override
    Comparator<OrderState> getOrderStateComparator() {
      return (o1, o2) -> o2.price.compareTo(o1.price);
    }
  }
}
