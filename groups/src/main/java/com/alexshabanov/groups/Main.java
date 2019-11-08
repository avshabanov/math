package com.alexshabanov.groups;

import com.alexshabanov.groups.finite.FiniteGroups;
import com.alexshabanov.groups.finite.cayley.CayleyGroup;
import lombok.experimental.UtilityClass;

import java.io.IOException;

@UtilityClass public class Main {

  public static void main(String[] args) throws IOException {
    FiniteGroups.ensureValid(CayleyGroup.INSTANCE);

    System.out.println("Cayley Group =");
    final StringBuilder sb = new StringBuilder(500);
    FiniteGroups.visualize(sb, CayleyGroup.INSTANCE);
    System.out.println(sb.toString());
  }
}
