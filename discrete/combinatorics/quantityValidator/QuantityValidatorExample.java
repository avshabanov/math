import java.util.*;

/**
 * Problem description: TBD
 *
 * @author Alexander Shabanov
 */
public final class QuantityValidatorExample {

  public static void main(String[] args) {
    final Decks decks1 = new Decks(Arrays.asList(
        new Deck(Arrays.asList("p1", "p2"), 0, 1),
        new Deck(Arrays.asList("p3", "p4"), 1, 1)
    ));

    demo(decks1, Collections.emptyList());
    demo(decks1, Collections.singletonList("p4"));
    demo(decks1, Collections.singletonList("p5"));
    demo(decks1, Arrays.asList("p2", "p4"));
    demo(decks1, Arrays.asList("p1", "p2", "p3"));
    demo(decks1, Arrays.asList("p1", "p2"));
    demo(decks1, Arrays.asList("p1", "p3"));
  }

  public static void demo(Decks decks, List<String> products) {
    final ValidationResult result = validate1(decks, products);
    System.out.println("decks=" + decks + " validated against products=" + products + "\n\tRESULT = " + result);
  }

  @SuppressWarnings("unused")
  interface ValidationResult {
    default boolean isOk() {
      return false;
    }

    default boolean isMinViolated() {
      return false;
    }

    default boolean isMaxViolated() {
      return false;
    }

    default Deck getOffendingDeck() {
      return null;
    }

    default String getOffendingProduct() {
      return null;
    }

    static ValidationResult ok() {
      return OkValidationResult.INSTANCE;
    }

    static ValidationResult minViolated(Deck deck) {
      return new MinConstraintValidationResult(deck);
    }

    static ValidationResult maxViolated(Deck deck) {
      return new MaxConstraintValidationResult(deck);
    }

    static ValidationResult ambiguousDeck(String product) {
      return new AmbiguousDeckProductValidationResult(product);
    }

    static ValidationResult missing(String product) {
      return new MissingProductValidationResult(product);
    }
  }

  // unoptimized, brute-force validation - simple, but O(n*m) complex
  @SuppressWarnings("Convert2streamapi")
  private static ValidationResult validate1(Decks decks, List<String> products) {
    final Set<String> productSet = new HashSet<>(products);

    for (final Deck deck : decks.decks) {
      int matches = 0;
      for (final String product : products) {
        for (final String deckProduct : deck.products) {
          if (product.equals(deckProduct)) {
            if (!productSet.contains(product)) {
              return ValidationResult.ambiguousDeck(product);
            }
            ++matches;
            productSet.remove(product);
          }
        }
      }

      if (matches < deck.min) {
        return ValidationResult.minViolated(deck);
      }

      if (matches > deck.max) {
        return ValidationResult.maxViolated(deck);
      }
    }

    if (!productSet.isEmpty()) {
      return ValidationResult.missing(productSet.iterator().next());
    }

    return ValidationResult.ok();
  }

  private static final class Decks {
    final List<Deck> decks;

    Decks(List<Deck> decks) {
      this.decks = Collections.unmodifiableList(Arrays.asList(decks.toArray(new Deck[decks.size()])));
    }

    @Override
    public String toString() {
      return "Decks{" +
          "decks=" + decks +
          '}';
    }
  }

  private static final class Deck {
    final List<String> products;
    final int min;
    final int max;

    Deck(List<String> products, int min, int max) {
      this.products = Collections.unmodifiableList(Arrays.asList(products.toArray(new String[products.size()])));
      this.min = min;
      this.max = max;
    }

    @Override
    public String toString() {
      return "Deck{" +
          "products=" + products +
          ", min=" + min +
          ", max=" + max +
          '}';
    }
  }

  private static final class OkValidationResult implements ValidationResult {
    private static final OkValidationResult INSTANCE = new OkValidationResult();

    @Override
    public boolean isOk() {
      return true;
    }

    @Override
    public String toString() {
      return "OK";
    }
  }

  private static abstract class DeckValidationResult implements ValidationResult {
    private final Deck deck;

    DeckValidationResult(Deck deck) {
      this.deck = deck;
    }

    @Override
    public Deck getOffendingDeck() {
      return deck;
    }
  }

  private static final class MinConstraintValidationResult extends DeckValidationResult {

    MinConstraintValidationResult(Deck deck) {
      super(deck);
    }

    @Override
    public boolean isMinViolated() {
      return true;
    }

    @Override
    public String toString() {
      return "MIN_VIOLATED{deck=" + getOffendingDeck() + "}";
    }
  }

  private static final class MaxConstraintValidationResult extends DeckValidationResult {

    MaxConstraintValidationResult(Deck deck) {
      super(deck);
    }

    @Override
    public boolean isMaxViolated() {
      return true;
    }

    @Override
    public String toString() {
      return "MAX_VIOLATED{deck=" + getOffendingDeck() + "}";
    }
  }

  private static abstract class ProductValidationResult implements ValidationResult {
    private final String product;

    ProductValidationResult(String product) {
      this.product = product;
    }

    @Override
    public String getOffendingProduct() {
      return product;
    }
  }

  private static final class AmbiguousDeckProductValidationResult extends ProductValidationResult {
    AmbiguousDeckProductValidationResult(String product) {
      super(product);
    }

    @Override
    public String toString() {
      return "AMBIGUOUS_DECK{product=" + getOffendingProduct() + "}";
    }
  }


  private static final class MissingProductValidationResult extends ProductValidationResult {
    MissingProductValidationResult(String product) {
      super(product);
    }

    @Override
    public String toString() {
      return "MISSING{product=" + getOffendingProduct() + "}";
    }
  }
}
