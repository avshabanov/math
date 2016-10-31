package com.alexshabanov.simulation.replication.logic.dummy;

import com.alexshabanov.simulation.replication.logic.ReplicatedOperation;
import com.alexshabanov.simulation.replication.logic.ReplicationListener;
import com.alexshabanov.simulation.replication.logic.Replicator;
import com.alexshabanov.simulation.replication.logic.SubscriptionResult;

import javax.annotation.ParametersAreNonnullByDefault;
import java.io.Serializable;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public final class DummyReplicator implements Replicator {
  public static final DummyReplicator INSTANCE = new DummyReplicator();

  private DummyReplicator() {}

  @Override
  public void replicate(ReplicatedOperation operation, String entityId, Serializable replicatedValue) {
    // do nothing
  }

  @Override
  public SubscriptionResult subscribe(String entityId, ReplicationListener listener) {
    return () -> {}; // do nothing
  }
}
