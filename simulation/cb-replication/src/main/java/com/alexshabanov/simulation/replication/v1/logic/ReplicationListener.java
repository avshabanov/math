package com.alexshabanov.simulation.replication.v1.logic;

/**
 * @author Alexander Shabanov
 */
public interface ReplicationListener {
  void applyReplicatedValue(ReplicatedOperation operation, Object value);
}
