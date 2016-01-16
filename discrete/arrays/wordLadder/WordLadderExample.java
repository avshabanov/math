import java.util.*;
import java.util.stream.Collectors;

/**
 * Sample run:
 * <pre>
 * Transformations from=hit to=cog using dictionary=[hot, dot, dog, lot, log] are: [hit, hot, dot, dog, cog]
 * No possible transformations from=hit to=cwg using given dictionary=[hot, dot, dog, lot, log]
 * Transformations from=hat to=sot using dictionary=[hot, dot, dog, lot, log] are: [hat, hot, sot]
 * Transformations from=man to=men using dictionary=[] are: [man, men]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class WordLadderExample {

  public static void main(String[] args) {
    demo("hit", "cog", Arrays.asList("hot","dot","dog","lot","log"));
    demo("hit", "cwg", Arrays.asList("hot","dot","dog","lot","log"));
    demo("hat", "sot", Arrays.asList("hot","dot","dog","lot","log"));
    demo("man", "men", Collections.emptyList());
  }

  static void demo(String from, String to, List<String> dictionary) {
    try {
      final List<String> transformations = getShortestLadder(from, to, dictionary);
      System.out.println("Transformations from=" + from + " to=" + to + " using dictionary=" + dictionary +
          " are: " + transformations);
    } catch (IllegalStateException e) {
      System.out.println("No possible transformations from=" + from + " to=" + to +
          " using given dictionary=" + dictionary);
    }
  }




  static List<String> getShortestLadder(String from, String to, List<String> dictionary) {
    // [1] build dictionary graph
    final List<WordNode> dictionaryNodes = new ArrayList<>(dictionary.size() + 1);
    final WordNode root = new WordNode(from);
    final Set<String> words = new HashSet<>((dictionary.size() + 1) * 2);
    words.add(to);
    dictionaryNodes.add(new WordNode(to));
    for (final String dictionaryEntry : dictionary) {
      if (words.contains(dictionaryEntry)) {
        continue;
      }
      words.add(dictionaryEntry);
      dictionaryNodes.add(new WordNode(dictionaryEntry));
    }

    // [2] find transformations between words
    buildTransformations(root, dictionaryNodes);
    dictionaryNodes.stream().forEach(n ->  buildTransformations(n, dictionaryNodes));

    // [3] find shortest path from root to term
    final List<WordNode> path = findShortestPath(root, to);
    return path.stream().map(n -> n.word).collect(Collectors.toList());
  }

  //
  // Private
  //

  private static List<WordNode> findShortestPath(WordNode from, String to) {
    final Set<String> words = new HashSet<>();
    final List<List<WordNode>> allPaths = new ArrayList<>(1);

    final List<WordNode> path = new ArrayList<>();
    path.add(from);
    findPath(words, from, to, path, allPaths);
    if (allPaths.isEmpty()) {
      throw new IllegalStateException("No possible transformation from word=" + from.word + " to word=" + to);
    }
    return allPaths.get(0);
  }

  private static void findPath(Set<String> usedWords,
                               WordNode node,
                               String to,
                               List<WordNode> path,
                               List<List<WordNode>> allPaths) {
    if (usedWords.contains(node.word)) {
      // already used? - return
      return;
    }

    if (to.equals(node.word)) {
      // path found - add it to allPath if it is the shortest one
      if (allPaths.isEmpty() || path.size() < allPaths.get(0).size()) {
        allPaths.clear();
        allPaths.add(new ArrayList<>(path));
      }
      return;
    }

    // iterate over all child nodes
    for (final WordNode child : node.nodes) {
      // update traversal state
      usedWords.add(node.word);
      path.add(child);

      // recurse
      findPath(usedWords, child, to, path, allPaths);

      // restore traversal state
      path.remove(path.size() - 1);
      usedWords.remove(node.word);
    }
  }

  private static void buildTransformations(WordNode from, List<WordNode> to) {
    to.stream().filter(n -> isOneLetterDifferent(from.word, n.word)).forEach(from.nodes::add);
  }

  private static boolean isOneLetterDifferent(String left, String right) {
    if (left.length() != right.length()) {
      return false; // only words of the same size can be transformed
    }

    int diff = 0;
    for (int i = 0; i < left.length(); ++i) {
      if (left.charAt(i) != right.charAt(i)) {
        ++diff;
        if (diff > 1) {
          break;
        }
      }
    }

    return diff == 1;
  }

  private static final class WordNode {
    final String word;
    final List<WordNode> nodes = new ArrayList<>();

    public WordNode(String word) {
      this.word = word;
    }

    @Override
    public String toString() {
      return "{word='" + word + "'}";
    }
  }
}
