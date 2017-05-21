package com.alexshabanov.simulation.replication.v2.logic.emu;

import com.alexshabanov.simulation.replication.v2.logic.Changeset;
import com.alexshabanov.simulation.replication.v2.logic.ReplicationNodeListener;
import com.alexshabanov.simulation.replication.v2.logic.Replicator;

import javax.annotation.ParametersAreNonnullByDefault;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public final class EmuReplicator implements Replicator {
  private List<ReplicationNodeListener> listeners;

  public EmuReplicator(Collection<ReplicationNodeListener> listeners) {
    this.listeners = Collections.unmodifiableList(Arrays
        .asList(listeners.toArray(new ReplicationNodeListener[listeners.size()])));
  }

  public void addListeners(Collection<ReplicationNodeListener> listeners) {
    this.listeners.addAll(listeners);
  }

  @Override
  public void replicate(Changeset changeset) {
  }

  @Override
  public long getNextSequenceId(String entity, boolean pullPreviousChangesets) {
    return 0;
  }
}
