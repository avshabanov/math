package com.alexshabanov.groups.finite;

import com.alexshabanov.groups.finite.cayley.CayleyGroup;
import com.alexshabanov.groups.finite.numbers.BaseNumericGroup;
import lombok.NonNull;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public final class FiniteGroupsTest {

  @Test
  public void shouldProduceStringRepresentationForCayleyGroup() throws IOException {
    final StringBuilder sb = new StringBuilder(500);
    FiniteGroups.visualize(sb, CayleyGroup.INSTANCE);
    final String visual = sb.toString();

    assertTrue("Should have 1", visual.contains(" 1 "));
    assertTrue("Should have -1", visual.contains(" -1 "));
    assertTrue("Should have i", visual.contains(" i "));
    assertTrue("Should have -i", visual.contains(" -i "));
  }

  @Test
  public void shouldEnsureCayleyGroupIsValid() {
    FiniteGroups.ensureValid(CayleyGroup.INSTANCE);
  }

  @Test
  public void shouldEnsureSingleIdentityElementGroupIsValid() {
    FiniteGroups.ensureValid(new NaiveNumericGroup(2));
  }

  @Test
  public void shouldFailClosureCheck() {
    try {
      FiniteGroups.ensureValid(new NaiveNumericGroup(3));
      fail("Naive group should fail closure property");
    } catch (NonGroupException e) {
      assertTrue(e.getMessage(), e.getMessage().contains("Closure violation"));
    }
  }

  private static final class NaiveNumericGroup extends BaseNumericGroup {

    NaiveNumericGroup(int to) {
      super(1, to);
    }

    @Override
    public Integer getIdentity() {
      return 1;
    }

    @Override
    public Integer mul(@NonNull Integer left, @NonNull Integer right) {
      return left * right;
    }
  }
}
