package com.alexshabanov.simulation.replication.v2.logic;

import javax.annotation.ParametersAreNonnullByDefault;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public interface Replicator {

  void replicate(Changeset changeset);

  long getNextSequenceId(String entity, boolean pullPreviousChangesets);
}
