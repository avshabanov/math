package com.alexshabanov.orderBook2;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.math.*;
import java.util.function.Predicate;

public final class SampleProcessor {
  private SampleProcessor() {} // hidden

  private static final String CONTENT1 = "limit buy 10 99.00\n" +
      "limit buy 15 100.00\n" +
      "limit buy 3 100.50\n" +
      "limit sell 5 100.00\n" +
      "limit buy 5 99.50\n" +
      "stop sell 3 99.49\n" +
      "cancel na 2 0.00\n" +
      "market sell 6 0.00";

  private static final String CONTENT2 = "limit sell 2 100.00\n" +
      "limit sell 5 105.00\n" +
      "limit sell 9 110.00\n" +
      "limit buy 4 120.00\n" +
      "limit buy 2 105.00\n" +
      "limit buy 1 90.00\n" +
      "limit buy 10 120.00";

  public static void main(String args[] ) throws Exception {
    final ByteArrayInputStream bais = new ByteArrayInputStream(CONTENT1.getBytes(StandardCharsets.UTF_8));

    try (final OrderParser parser = new DefaultOrderParser(new InputStreamReader(bais))) {
      final OrderProcessor processor = new DefaultOrderProcessor(new PrintStreamMatcherReporter(System.out));
      processor.run(parser.iterator());
    }
  }
}

//
// Order Model
//

/**
 * Represents an order state, either buy or sell.
 */
enum OrderSide {
  BUY,
  SELL
}

/**
 * Represents an order type, except for cancel orders which are handled in order of appearance.
 * See also BookEntry and order processor implementation for details on handling orders.
 */
enum OrderKind {
  MARKET,
  LIMIT,
  STOP
}

/**
 * Represents an interface to order object (except for cancel orders).
 *
 */
interface Order {
  /**
   * @return Positive 1-started order position
   */
  int getPosition();

  /**
   * @return Type of an order
   */
  OrderKind getKind();

  /**
   * @return Side of an order
   */
  OrderSide getSide();

  /**
   * Determines if this order has price attribute.
   * False for market orders, true for all the others.
   *
   * @return True, if this object has readable price attribute, false otherwise
   */
  boolean hasPrice();

  /**
   * @return Price of this order
   * @throws IllegalStateException If price attribute is not available (market orders)
   */
  BigDecimal getPrice();

  /**
   * @return Current trade count
   */
  int getTradeCount();

  /**
   * Sets trade count to the given value.
   *
   * @param value New trade count value
   */
  void setTradeCount(int value);

  default void decrementTradeCount(int delta) {
    setTradeCount(getTradeCount() - delta);
  }
}

/**
 * Represents an order (except for cancel orders).
 */
abstract class AbstractOrder implements Order {
  private final int position;
  private final OrderSide side;
  private int tradeCount; // mutable

  AbstractOrder(int position, OrderSide side, int tradeCount) {
    if (position <= 0) {
      throw new IllegalArgumentException("position");
    }

    if (tradeCount <= 0) {
      throw new IllegalArgumentException("tradeCount");
    }

    this.position = position;
    this.side = Objects.requireNonNull(side, "side");
    this.tradeCount = tradeCount;
  }

  @Override
  public final int getPosition() {
    return position;
  }

  @Override
  public final OrderSide getSide() {
    return side;
  }

  @Override
  public final int getTradeCount() {
    return tradeCount;
  }

  @Override
  public void setTradeCount(int value) {
    if (value < 0) {
      throw new IllegalArgumentException("tradeCount value can not be negative");
    }
    this.tradeCount = value;
  }

  @Override
  public boolean hasPrice() {
    return false;
  }

  @Override
  public BigDecimal getPrice() {
    throw new IllegalStateException("Object of this type does not have price attribute");
  }

  @Override public final String toString() {
    return String.format("%d %s %s %d %s", position, getKind(), side, tradeCount, hasPrice() ? getPrice() : "na");
  }
}

abstract class AbstractOrderWithPrice extends AbstractOrder {
  private final BigDecimal price;

  AbstractOrderWithPrice(int position, OrderSide side, int tradeCount, BigDecimal price) {
    super(position, side, tradeCount);

    if (price == null || price.compareTo(BigDecimal.ZERO) <= 0) {
      throw new IllegalArgumentException("price");
    }

    this.price = price;
  }

  @Override
  public final boolean hasPrice() {
    return true;
  }

  @Override
  public final BigDecimal getPrice() {
    return price;
  }
}

final class LimitOrder extends AbstractOrderWithPrice {
  LimitOrder(int position, OrderSide side, int tradeCount, BigDecimal price) {
    super(position, side, tradeCount, price);
  }

  @Override
  public OrderKind getKind() {
    return OrderKind.LIMIT;
  }
}

final class MarketOrder extends AbstractOrder {
  MarketOrder(int position, OrderSide side, int tradeCount) {
    super(position, side, tradeCount);
  }

  @Override
  public OrderKind getKind() {
    return OrderKind.MARKET;
  }
}

final class StopOrder extends AbstractOrderWithPrice {
  StopOrder(int position, OrderSide side, int tradeCount, BigDecimal price) {
    super(position, side, tradeCount, price);
  }

  @Override
  public OrderKind getKind() {
    return OrderKind.STOP;
  }
}

//
// Parser Interface
//

interface BookEntry {
  boolean isCancel();
  int getCancelPosition();
  Order getOrder();
}

interface OrderParser extends Closeable {

  BookEntry parseNext(int position) throws IOException;

  /**
   * @return Iterator interface to this parser
   */
  default Iterator<BookEntry> iterator() {
    return new OrderParserIterator(this);
  }
}

/**
 * Helper class that represents parsed book entries as iterator
 */
final class OrderParserIterator implements Iterator<BookEntry> {
  private final OrderParser parser;
  private int position;
  private BookEntry nextElement;

  OrderParserIterator(OrderParser parser) {
    this.parser = parser;
    this.nextElement = tryParseNext();
  }

  @Override
  public boolean hasNext() {
    return nextElement != null;
  }

  @Override
  public BookEntry next() {
    if (nextElement == null) {
      throw new NoSuchElementException();
    }

    final BookEntry result = nextElement;
    nextElement = tryParseNext();
    return result;
  }

  private BookEntry tryParseNext() {
    try {
      ++position;
      return parser.parseNext(position);
    } catch (IOException e) {
      throw new IllegalStateException(e);
    }
  }
}

//
// Parser Implementation
//

final class CancelBookEntry implements BookEntry {
  private final int cancelPosition;

  CancelBookEntry(int cancelPosition) {
    this.cancelPosition = cancelPosition;
  }

  @Override
  public boolean isCancel() {
    return true;
  }

  @Override
  public int getCancelPosition() {
    return cancelPosition;
  }

  @Override
  public Order getOrder() {
    throw new IllegalStateException();
  }
}

final class OrderBookEntry implements BookEntry {
  private final Order order;

  OrderBookEntry(Order order) {
    this.order = order;
  }

  @Override
  public boolean isCancel() {
    return false;
  }

  @Override
  public int getCancelPosition() {
    throw new IllegalStateException();
  }

  @Override
  public Order getOrder() {
    return order;
  }
}

final class DefaultOrderParser implements OrderParser {
  private final BufferedReader reader;

  DefaultOrderParser(Reader reader) {
    this.reader = new BufferedReader(reader);
  }

  @Override
  public BookEntry parseNext(int position) throws IOException {
    final String line = this.reader.readLine();
    if (line == null) {
      return null; // end of input
    }

    final String[] tokens = line.split(" ");
    if (tokens.length != 4) {
      throw new IOException("Unexpected token count");
    }

    switch (tokens[0]) {
      case "market":
        return new OrderBookEntry(new MarketOrder(position, parseOrderSide(tokens[1]), Integer.parseInt(tokens[2])));
      case "limit":
        return new OrderBookEntry(new LimitOrder(position, parseOrderSide(tokens[1]),
            Integer.parseInt(tokens[2]), new BigDecimal(tokens[3])));
      case "stop":
        return new OrderBookEntry(new StopOrder(position, parseOrderSide(tokens[1]),
            Integer.parseInt(tokens[2]), new BigDecimal(tokens[3])));
      case "cancel":
        return new CancelBookEntry(Integer.parseInt(tokens[2]));
    }

    throw new IOException("Unknown order type=" + tokens[0]);
  }

  @Override
  public void close() throws IOException {
    this.reader.close();
  }

  private static OrderSide parseOrderSide(String token) throws IOException {
    if ("buy".equals(token)) {
      return OrderSide.BUY;
    } else if ("sell".equals(token)) {
      return OrderSide.SELL;
    }

    throw new IOException("Illegal order side=" + token);
  }
}

//
// Matcher reporter
//

/**
 * Interface to the object that reports about found matches in the book order log.
 */
interface MatcherReporter {

  /**
   * Reports about found match in the order log.
   *
   * @param positionTaken Position of the order that was executed
   * @param positionMaker Position in the order that was matched to the executed order
   * @param volume Number of items traded
   * @param price Trading price
   */
  void onMatch(
      int positionTaken,
      int positionMaker,
      int volume,
      BigDecimal price);
}

final class PrintStreamMatcherReporter implements MatcherReporter {
  private final PrintStream out;

  PrintStreamMatcherReporter(PrintStream out) {
    this.out = Objects.requireNonNull(out, "out");
  }

  @Override
  public void onMatch(int positionTaken, int positionMaker, int volume, BigDecimal price) {
    out.println(String.format("match %d %d %d %s", positionTaken, positionMaker, volume, price));
  }
}

//
// Processor Interface
//

interface OrderProcessor {

  /**
   * Applies order processor to the given stream
   *
   * @param parserResults Parser results
   */
  void run(Iterator<BookEntry> parserResults);
}

//
// Processor Implementation
//

final class DefaultOrderProcessor implements OrderProcessor {
  private final MatcherReporter matcherReporter;

  // enacted (currently processing) order lists
  private final Map<Integer, Order> activeOrders = new HashMap<>();

  private final List<Order> buyLimitOrders = new ArrayList<>();
  private final List<Order> sellLimitOrders = new ArrayList<>();
  private final List<Order> buyStopOrders = new ArrayList<>();
  private final List<Order> sellStopOrders = new ArrayList<>();
  private final List<Order> buyMarketOrders = new ArrayList<>();
  private final List<Order> sellMarketOrders = new ArrayList<>();

  DefaultOrderProcessor(MatcherReporter matcherReporter) {
    this.matcherReporter = matcherReporter;
  }

  @Override
  public void run(Iterator<BookEntry> parserResults) {
    while (parserResults.hasNext()) {
      final BookEntry bookEntry = parserResults.next();

      if (bookEntry.isCancel()) {
        //out.println("\t- Adding cancel request for position : " + bookEntry.getCancelPosition());
        removeOrderAt(bookEntry.getCancelPosition());
      } else {
        //out.println("\t- Adding order #" + bookEntry.getOrder().position + " : " + bookEntry.getOrder());
        triggerOrderProcessing(bookEntry.getOrder());
      }
    }
  }

  private void triggerOrderProcessing(Order order) {
    activeOrders.put(order.getPosition(), order);

    switch (order.getKind()) {
      case LIMIT:
        processLimitOrder(order);
        break;

      case STOP:
        processStopOrder(order);
        break;

      case MARKET:
        processMarketOrder(order);
        break;

      default:
        throw new IllegalStateException();
    }

    postProcessOrders();
  }

  private void postProcessOrders() {
    processMarketOrders(buyMarketOrders, sellLimitOrders);
    processMarketOrders(sellMarketOrders, buyLimitOrders);
  }

  private void processMarketOrders(List<Order> marketOrders, List<Order> opposingLimitOrders) {
    final int prevSize = marketOrders.size();

    // iterate over a copy of market orders to avoid concurrent modification exception caused by
    // potential interference with the stop orders
    final Set<Integer> removePositions = new HashSet<>();
    for (Order order : new ArrayList<>(marketOrders)) {
      executeTradingOrder(order, opposingLimitOrders, o -> true);
      if (order.getTradeCount() == 0) {
        removePositions.add(order.getPosition());
      }
    }

    final int currentSize = marketOrders.size();

    // remove all the marked positions
    marketOrders.removeIf(o -> removePositions.contains(o.getPosition()));

    // mismatch of current vs previous size is an indication that stop order has been added,
    // so reprocess current orders again
    if (prevSize != currentSize) {
      processMarketOrders(marketOrders, opposingLimitOrders);
    }
  }

  private void removeOrderAt(int targetPosition) {
    final Order removedOrder = this.activeOrders.remove(targetPosition);
    if (removedOrder == null) {
      return;
    }

    // set trade count for this order to zero and then this order will be eventually recycled
    removedOrder.setTradeCount(0);
  }

  private void executeTradingOrder(
      Order order,
      List<Order> opposingSideOrders,
      Predicate<Order> orderFilter /* TODO: optimization - use start position */) {
    for (Iterator<Order> it = opposingSideOrders.iterator(); it.hasNext();) {
      if (order.getTradeCount() == 0) {
        return; // current limit order has been fulfilled
      }

      final Order o = it.next();
      if (!orderFilter.test(o)) {
        continue;
      }

      if (o.getTradeCount() > 0) {
        final int count = Math.min(order.getTradeCount(), o.getTradeCount());
        o.decrementTradeCount(count);
        order.decrementTradeCount(count);

        // pick either limit price of opposing order or current order's price
        final BigDecimal matchingPrice = o.hasPrice() ? o.getPrice() : order.getPrice();
        matcherReporter.onMatch(order.getPosition(), o.getPosition(), count, matchingPrice);

        if (order.getSide() == OrderSide.BUY && !buyStopOrders.isEmpty()) {
          // this is a buy, process buy-stop orders
          for (final Iterator<Order> sit = buyStopOrders.iterator(); sit.hasNext();) {
            final Order buyStopOrder = sit.next();
            if (matchingPrice.compareTo(buyStopOrder.getPrice()) >= 0) {
              sit.remove();
              insertNewOrder(
                  buyMarketOrders,
                  new MarketOrder(buyStopOrder.getPosition(), buyStopOrder.getSide(), buyStopOrder.getTradeCount()),
                  POSITION_ORDER_COMPARATOR);
            }
          }
        } else if (!sellStopOrders.isEmpty()) {
          // this is a sell, process sell-stop orders
          for (final Iterator<Order> sit = sellStopOrders.iterator(); sit.hasNext();) {
            final Order sellStopOrder = sit.next();
            if (matchingPrice.compareTo(sellStopOrder.getPrice()) <= 0) {
              sit.remove();
              insertNewOrder(
                  sellMarketOrders,
                  new MarketOrder(sellStopOrder.getPosition(), sellStopOrder.getSide(), sellStopOrder.getTradeCount()),
                  POSITION_ORDER_COMPARATOR);
            }
          }
        }
      }

      if (o.getTradeCount() == 0) {
        it.remove(); // opposing order has been fulfilled
      }
    }
  }

  private static void insertNewOrder(List<Order> orders, Order newOrder, Comparator<Order> comparator) {
    final int insertIndex = Collections.binarySearch(orders, newOrder, comparator);
    if (insertIndex >= 0) {
      throw new IllegalStateException();
    }

    orders.add(-insertIndex - 1, newOrder);
  }

  private void processLimitOrder(Order limitOrder) {
    if (limitOrder.getSide() == OrderSide.BUY) {
      // execute at or below limit price against other sell limit orders
      executeTradingOrder(limitOrder, sellLimitOrders, o -> o.getPrice().compareTo(limitOrder.getPrice()) <= 0);

      // execute at limit price against unfulfilled sell market orders
      executeTradingOrder(limitOrder, sellMarketOrders, o -> true);
    } else {
      // execute at or above limit price against other buy limit orders
      executeTradingOrder(limitOrder, buyLimitOrders, o -> o.getPrice().compareTo(limitOrder.getPrice()) >= 0);

      // execute at limit price against unfulfilled buy market orders
      executeTradingOrder(limitOrder, buyMarketOrders, o -> true);
    }

    // abstain from inserting this order if it has been fulfilled
    if (limitOrder.getTradeCount() == 0) {
      return;
    }

    // limit order has not been fully processed, insert it for further processing
    if (limitOrder.getSide() == OrderSide.BUY) {
      insertNewOrder(buyLimitOrders, limitOrder, BUY_LIMIT_ORDER_COMPARATOR);
    } else {
      insertNewOrder(sellLimitOrders, limitOrder, SELL_LIMIT_ORDER_COMPARATOR);
    }
  }

  private static final Comparator<Order> BUY_LIMIT_ORDER_COMPARATOR = (o1, o2) -> {
    final int priceCompareResult = o2.getPrice().compareTo(o1.getPrice());
    if (priceCompareResult == 0) {
      // take into an account order of appearance
      return Integer.compare(o1.getPosition(), o2.getPosition());
    }
    return priceCompareResult;
  };

  private static final Comparator<Order> SELL_LIMIT_ORDER_COMPARATOR = (o1, o2) -> {
    final int priceCompareResult = o1.getPrice().compareTo(o2.getPrice());
    if (priceCompareResult == 0) {
      // take into an account order of appearance
      return Integer.compare(o1.getPosition(), o2.getPosition());
    }
    return priceCompareResult;
  };

  private static final Comparator<Order> POSITION_ORDER_COMPARATOR =
      (o1, o2) -> Integer.compare(o1.getPosition(), o2.getPosition());

  private void processStopOrder(Order stopOrder) {
    if (stopOrder.getSide() == OrderSide.BUY) {
      insertNewOrder(buyStopOrders, stopOrder, POSITION_ORDER_COMPARATOR);
    } else {
      insertNewOrder(sellStopOrders, stopOrder, POSITION_ORDER_COMPARATOR);
    }
  }

  private void processMarketOrder(Order marketOrder) {
    if (marketOrder.getSide() == OrderSide.BUY) {
      // execute against other sell limit orders
      executeTradingOrder(marketOrder, sellLimitOrders, o -> true);
      if (marketOrder.getTradeCount() > 0) {
        insertNewOrder(buyMarketOrders, marketOrder, POSITION_ORDER_COMPARATOR);
      }
    } else {
      // execute against other buy limit orders
      executeTradingOrder(marketOrder, buyLimitOrders, o -> true);
      if (marketOrder.getTradeCount() > 0) {
        insertNewOrder(sellMarketOrders, marketOrder, POSITION_ORDER_COMPARATOR);
      }
    }
  }
}
