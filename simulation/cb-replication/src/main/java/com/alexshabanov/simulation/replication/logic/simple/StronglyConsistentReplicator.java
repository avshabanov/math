package com.alexshabanov.simulation.replication.logic.simple;

import com.alexshabanov.simulation.replication.logic.ReplicatedOperation;
import com.alexshabanov.simulation.replication.logic.ReplicationListener;
import com.alexshabanov.simulation.replication.logic.Replicator;
import com.alexshabanov.simulation.replication.logic.SubscriptionResult;

import javax.annotation.ParametersAreNonnullByDefault;
import java.io.Serializable;
import java.util.*;

/**
 * Simple strongly consistent replicator, that expects response from all the nodes in the replication group.
 *
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public final class StronglyConsistentReplicator implements Replicator {
  private List<StronglyConsistentReplicator> group;
  private final String nodeName; // name of this node, shall be unique within the group

  public StronglyConsistentReplicator(String nodeName) {
    this.nodeName = nodeName;
    this.group = Collections.emptyList();
  }

  public void setGroup(List<StronglyConsistentReplicator> replicators) {
    final List<StronglyConsistentReplicator> groupCopy = Collections.unmodifiableList(Arrays.asList(
        replicators.toArray(new StronglyConsistentReplicator[replicators.size()])));
    assertNodeNamesAreUnique(nodeName, groupCopy);
    this.group = groupCopy;
  }

  @Override
  public void replicate(ReplicatedOperation operation, String entityId, Serializable replicatedValue) {
    for (final StronglyConsistentReplicator r : group) {
      if (r.nodeName.equals(nodeName)) {
        continue; // replicate to self is not allowed
      }

      r.propagate(operation, entityId, replicatedValue);
    }
  }

  @Override
  public SubscriptionResult subscribe(String entityId, ReplicationListener listener) {
    return null;
  }

  public void propagate(ReplicatedOperation operation, String entityId, Serializable replicatedValue) {
    // TODO: implement
  }

  //
  // Private
  //

  private static void assertNodeNamesAreUnique(String nodeName, List<StronglyConsistentReplicator> group) {
    final Set<String> names = new HashSet<>((1 + group.size()) * 2);
    names.add(nodeName);
    for (final StronglyConsistentReplicator r : group) {
      if (!names.add(r.nodeName)) {
        throw new IllegalStateException("Invalid replicator group; duplicate nodeName=" + nodeName);
      }
    }
  }
}
