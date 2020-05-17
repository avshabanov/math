package problems.leet100.challenges.c2020_05.w2;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * https://leetcode.com/explore/challenge/card/may-leetcoding-challenge/535/week-2-may-8th-may-14th/3325/
 * <p>In a town, there are N people labelled from 1 to N.
 * There is a rumor that one of these people is secretly the town judge.
 *
 * If the town judge exists, then:
 *
 * The town judge trusts nobody.
 * Everybody (except for the town judge) trusts the town judge.
 * There is exactly one person that satisfies properties 1 and 2.
 * You are given trust, an array of pairs trust[i] = [a, b] representing that
 * the person labelled a trusts the person labelled b.
 *
 * If the town judge exists and can be identified, return the label of the town judge.  Otherwise, return -1.</p>
 * <p>
 * Note:
 *
 * 1 <= N <= 1000
 * trust.length <= 10000
 * trust[i] are all different
 * trust[i][0] != trust[i][1]
 * 1 <= trust[i][0], trust[i][1] <= N
 * </p>
 */
public class FindTownJudgeSolution {

  public static final class Demo1 {
    public static void main(String[] args) {
      final int n = 4;
      final int[][] trust = {
          {1, 2}, {1, 3}, {1, 4}, {2, 4}, {4, 3}, {2, 3}
      };

      final int judge = findJudge(n, trust);
      System.out.printf("Demo1: judge=%d\n", judge);
    }
  }

  public static final class Demo2 {
    public static void main(String[] args) {
      final int n = 3;
      final int[][] trust = {
          {1, 3}, {2, 3}, {3, 1}
      };

      final int judge = findJudge(n, trust);
      System.out.printf("Demo1: judge=%d\n", judge);
    }
  }

  private static int findJudge(int n, int[][] trust) {
    if (trust.length == 0) {
      return n == 1 ? 1 : 0;
    }

    // for each person: "how many people do I trust?"
    final Map<Integer, Integer> participantTrustNum = new HashMap<>();

    // for each person: "how many people trust me?"
    final Map<Integer, Integer> participantToTrust = new HashMap<>();
    for (final int[] pair : trust) {
      participantToTrust.compute(pair[1], (k, v) -> v == null ? 1 : v + 1);
      participantTrustNum.compute(pair[0], (k, v) -> v == null ? 1 : v + 1);
    }

    // sort by number of people who trust this person
    final List<Map.Entry<Integer, Integer>> participantTrustSorted = new ArrayList<>(participantToTrust.entrySet());
    participantTrustSorted.sort((l, r) -> r.getValue().compareTo(l.getValue()));

    // finally verify that there is a first entry and it is only one collecting (n-1) people who trust this person
    Map.Entry<Integer, Integer> judge = null;
    for (Map.Entry<Integer, Integer> person : participantTrustSorted) {
      if (person.getValue() != (n - 1)) {
        // stop looking further: next entries will contain less than expected
        // number of persons who trust corresponding person
        break;
      }

      if (participantTrustNum.getOrDefault(person.getKey(), 0) > 0) {
        // even though everybody trust this person, it trusts someone so it could not be a judge
        continue;
      }

      if (judge == null) {
        // found judge candidate: it trusts no one yet n-1 people trust him
        judge = person;
      } else {
        // more than one judge
        judge = null;
        break;
      }
    }

    return judge != null ? judge.getKey() : -1;
  }
}
