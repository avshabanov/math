package com.alexshabanov.groups.finite;

import com.alexshabanov.groups.finite.cayley.CayleyGroup;
import com.alexshabanov.groups.finite.numbers.BaseNumericGroup;
import com.google.common.collect.ImmutableList;
import lombok.NonNull;
import org.junit.Test;

import java.io.IOException;
import java.util.List;

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
  public void shouldEnsureComplementOnesGroupIsValid() {
    FiniteGroups.ensureValid(new ComplementOnesGroup());
  }

  @Test
  public void shouldFailClosureCheck() {
    try {
      FiniteGroups.ensureValid(new NaiveNumericGroup(3));
      fail("Naive group should fail closure check");
    } catch (NonGroupException e) {
      assertTrue(e.getMessage(), e.getMessage().contains("Closure violation"));
    }
  }

  @Test
  public void shouldFailInverseElementCheck() {
    try {
      FiniteGroups.ensureValid(new NonInversableGroup(3));
      fail("Naive group should fail inverse element check");
    } catch (NonGroupException e) {
      assertTrue(e.getMessage(), e.getMessage().contains("Inverse element violation"));
    }
  }

  @Test
  public void shouldFailInverseElementAllegianceCheck() {
    try {
      FiniteGroups.ensureValid(new ComplementOnesGroup() {
        @Override public Integer getIdentity() { return 0; }
      });
      fail("Complement ones group should not contain zero");
    } catch (NonGroupException e) {
      assertTrue(e.getMessage(), e.getMessage().contains("Identity element 0 does not belong to a group"));
    }
  }

  //
  // Private
  //

  private static class NaiveNumericGroup extends BaseNumericGroup {

    NaiveNumericGroup(int to) {
      super(1, to);
    }

    @Override public Integer getIdentity() {
      return 1;
    }

    @Override public Integer mul(@NonNull Integer left, @NonNull Integer right) {
      return left * right;
    }
  }

  private static final class NonInversableGroup extends NaiveNumericGroup {
    NonInversableGroup(int to) {
      super(to);
    }

    @Override public Integer mul(@NonNull Integer left, @NonNull Integer right) {
      return left;
    }
  }

  private static class ComplementOnesGroup implements FiniteGroup<Integer> {
    @Override public Integer getIdentity() { return 1; }
    @Override public @NonNull List<Integer> getElements() { return ImmutableList.of(-1, 1); }
    @Override public Integer mul(@NonNull Integer left, @NonNull Integer right) { return left * right; }

    @Override public String toString() { return "{-1, 1}"; }
  }
}
