package com.alexshabanov.simulation.replication.logic;

/**
 * @author Alexander Shabanov
 */
public interface ReplicationListener {
  void applyReplicatedValue(ReplicatedOperation operation, Object value);
}
