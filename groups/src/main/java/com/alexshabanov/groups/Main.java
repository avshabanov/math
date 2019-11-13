package com.alexshabanov.groups;

import com.alexshabanov.groups.finite.FiniteGroup;
import com.alexshabanov.groups.finite.FiniteGroups;
import com.alexshabanov.groups.finite.adhoc.CayleyGroup;
import com.alexshabanov.groups.finite.adhoc.SquareSymmetryGroup;
import com.alexshabanov.groups.finite.numbers.IntRangeGroup;
import com.alexshabanov.groups.finite.numbers.ComplementOnesGroup;
import lombok.NonNull;
import lombok.experimental.UtilityClass;

import java.io.IOException;

@UtilityClass public class Main {

  public static void main(String[] args) throws IOException {
    System.out.println("= Finite Groups Demo =\n");

    demoFiniteGroup("({0, 1, 2, 3}, +) Group", new IntRangeGroup(0, 4) {
      @Override public Integer getIdentity() { return 0; }
      @Override public Integer mul(@NonNull Integer left, @NonNull Integer right) { return (left + right) % 4; }
    });
    demoFiniteGroup("({-1, 1}, *) Group", ComplementOnesGroup.INSTANCE);
    demoFiniteGroup("({-1, 1, i, -i}, *) - Cayley Group", CayleyGroup.INSTANCE);
    demoFiniteGroup("D4 Cube Group", SquareSymmetryGroup.INSTANCE);
  }

  private static <T> void demoFiniteGroup(String groupName, FiniteGroup<T> group) throws IOException {
    final StringBuilder sb = new StringBuilder(500);

    FiniteGroups.ensureValid(group);
    System.out.println(groupName + " =");
    sb.setLength(0);
    FiniteGroups.visualize(sb, group);
    System.out.println(sb.toString());
  }
}
