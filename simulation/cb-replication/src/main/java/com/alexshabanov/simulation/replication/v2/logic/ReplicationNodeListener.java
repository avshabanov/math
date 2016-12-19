package com.alexshabanov.simulation.replication.v2.logic;

/**
 * @author Alexander Shabanov
 */
public interface ReplicationNodeListener {

  void applyChangeset(Changeset changeset);
}
