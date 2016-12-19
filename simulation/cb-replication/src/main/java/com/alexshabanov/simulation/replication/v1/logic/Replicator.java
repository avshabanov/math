package com.alexshabanov.simulation.replication.v1.logic;

import javax.annotation.ParametersAreNonnullByDefault;
import java.io.Serializable;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public interface Replicator {

  void replicate(ReplicatedOperation operation, String entityId, Serializable replicatedValue);

  SubscriptionResult subscribe(String entityId, ReplicationListener listener);
}
