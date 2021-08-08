package problems.computations;

import java.util.Arrays;
import java.util.List;
import java.util.OptionalInt;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Verifies information propagation rate in a distributed system using enhanced random choice algorithm.
 */
public class Gossips {

  public static final class Demo1 {
    public static void main(String[] args) {
      final int participantCount = 1000;
      final List<Participant> participants = IntStream.range(1, 1 + participantCount).mapToObj(Participant::new)
          .collect(Collectors.toList());

      final GossipAlgorithm gossipAlgorithm = pickGossipAlgorithm(args);
      final int iterations = 10000;
      final int accumulatedFactSum = (participantCount * (participantCount + 1)) / 2;
      boolean alternatingFactFlag = false;
      final Statistics statistics = new Statistics();
      for (int i = 0; i < iterations; ++i) {
        alternatingFactFlag = !alternatingFactFlag;
        int accumulatedFacts = 1;
        participants.get(0).alternatingFactFlag = alternatingFactFlag;
        int learnIterations = 0;
        for (; accumulatedFacts != accumulatedFactSum; learnIterations++) {
          for (final Participant p : participants) {
            if (p.alternatingFactFlag != alternatingFactFlag) {
              continue; // this participant knows nothing about current fact yet
            }

            final OptionalInt gossipedParticipantId = gossipAlgorithm.gossip(participants, alternatingFactFlag);
            if (gossipedParticipantId.isPresent()) {
              // record participant who already knows about this fact
              accumulatedFacts += gossipedParticipantId.getAsInt();
            }
          }
          statistics.record(learnIterations, false);
        } //< learn iterations
        statistics.record(learnIterations, true);
      } //< attempted iterations

      System.out.println("(* Using " + gossipAlgorithm + " gossip algorithm *)");
      System.out.println("(* Total number of participants: " + participantCount + " *)");
      statistics.report(); //< finally report collected statistics
    }
  }

  private static final class Statistics {
    static final int MAX_ITERATIONS = 1_000_000_000;

    int minIterations = Integer.MAX_VALUE;
    int maxIterations;
    long iterationsSum;
    int numberOfReports;

    void record(int numIterations, boolean finalReport) {
      if (!finalReport) {
        if (numIterations > MAX_ITERATIONS) {
          throw new RuntimeException("Too many attempts");
        }
        return;
      }
      //System.out.printf("All participants learned about gossiped fact after %d iteration(s)\n", numIterations);
      minIterations = Math.min(minIterations, numIterations);
      maxIterations = Math.max(maxIterations, numIterations);
      iterationsSum += numIterations;
      ++numberOfReports;
    }

    void report() {
      System.out.printf(
          "Statistics:\n" +
              "Min iterations: %d\n" +
              "Max iterations: %d\n" +
              "Avg iterations: %.2f\n",
          minIterations,
          maxIterations,
          iterationsSum * 1.0 / numberOfReports
      );
    }
  }

  private static final class Participant {
    final int id;
    boolean alternatingFactFlag;
    public Participant(int id) {
      this.id = id;
    }

    @Override public String toString() {
      return "Participant{" + "id=" + id + ", aff=" + alternatingFactFlag + '}';
    }
  }

  private static final Random RANDOM = new Random(1007);

  private static GossipAlgorithm pickGossipAlgorithm(String[] args) {
    if (!Arrays.asList(args).contains("-use1")) {
      return SIMPLE_GOSSIP_ALGORITHM;
    }
    return TWO_ATTEMPTS_GOSSIP_ALGORITHM;
  }

  private interface GossipAlgorithm {
    OptionalInt gossip(List<Participant> participants, boolean alternatingFactFlag);
  }

  private static final GossipAlgorithm SIMPLE_GOSSIP_ALGORITHM = (participants, alternatingFactFlag) -> {
    //  try gossiping about known fact to some neighbor
    final Participant other = participants.get(RANDOM.nextInt(participants.size()));
    if (other.alternatingFactFlag == alternatingFactFlag) {
      return OptionalInt.empty();
    }
    other.alternatingFactFlag = alternatingFactFlag;
    return OptionalInt.of(other.id);
  };

  private static final GossipAlgorithm TWO_ATTEMPTS_GOSSIP_ALGORITHM = (participants, alternatingFactFlag) -> {
    //  try gossiping about known fact to some neighbor
    Participant other = null;
    for (int i = 0; i < 2; i++) {
      other = participants.get(RANDOM.nextInt(participants.size()));
      if (other.alternatingFactFlag == alternatingFactFlag) {
        other = null;
      }
    }

    if (other == null) {
      return OptionalInt.empty();
    }

    other.alternatingFactFlag = alternatingFactFlag;
    return OptionalInt.of(other.id);
  };
}
