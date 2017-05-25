package com.alexshabanov.simulation.replication.v3.logic;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ThreadPoolExecutor;

public final class Replication {

  public interface ReplicationActionSettings {
  }

  public enum StandardReplicationActionSettings implements ReplicationActionSettings {
    DEFAULT
  }

  public interface ReplicatedEntity {

    byte[] getBytes();
    int getBytesOffset();
    int getBytesLength();
  }

  public interface Replicator {

    void replicate(
        ReplicatedEntity entity,
        ReplicationActionSettings settings);

    default void replicate(ReplicatedEntity entity) {
      replicate(entity, StandardReplicationActionSettings.DEFAULT);
    }
  }

  public interface ReplicationCallback {

    void applyReplicatedEntity(ReplicatedEntity entity);
  }

  //
  // Local Emulation
  //

  public static final class ReplicatedChangeset {
    final List<ReplicatedEntity> entities;

    public ReplicatedChangeset(List<ReplicatedEntity> entities) {
      this.entities = entities;
    }
  }

  public interface ReplicationNode {

    // incoming request to process changeset
    void processChangeset(ReplicatedChangeset changeset);
  }

  public static final class ReplicationManager implements ReplicationNode, Replicator {
    private final ReplicationCallback replicationCallback;
    private final List<ReplicationNode> replicationNodes = new CopyOnWriteArrayList<>();
    private final ExecutorService executorService;

    public ReplicationManager(ReplicationCallback replicationCallback, ExecutorService executorService) {
      this.replicationCallback = Objects.requireNonNull(replicationCallback);
      this.executorService = Objects.requireNonNull(executorService);
    }

    public void processChangeset(ReplicatedChangeset changeset) {
      for (final ReplicatedEntity entity : changeset.entities) {
        replicationCallback.applyReplicatedEntity(entity);
      }
    }

    @Override
    public void replicate(ReplicatedEntity entity, ReplicationActionSettings settings) {
    }
  }

  public interface ReplicationController {
    Replicator getReplicator();
    ReplicationNode getReplicationNode();
  }

  public interface LocalReplicationController extends ReplicationController {
    void setDelay(long delay);
  }

  public interface LocalReplicationControllers {
    LocalReplicationController getReplicationController(int controllerIndex);

    default void setDelay(int controllerIndex, long delay) {
      getReplicationController(controllerIndex).setDelay(delay);
    }
  }

  public static final class LocalReplicationControllersImpl implements LocalReplicationControllers {
    final List<LocalReplicationController> controllers;

    public LocalReplicationControllersImpl(List<LocalReplicationController> controllers) {
      this.controllers = controllers;
    }

    @Override
    public LocalReplicationController getReplicationController(int controllerIndex) {
      return controllers.get(controllerIndex);
    }
  }

  public static final class LocalReplicationClusterSettings {
    private final int size;

    private LocalReplicationClusterSettings(int size) {
      this.size = size;
    }

    public int getSize() {
      return size;
    }

    public static Builder newBuilder() {
      return new Builder();
    }

    public static final class Builder {
      private int size = 1;

      public LocalReplicationClusterSettings build() {
        return new LocalReplicationClusterSettings(size);
      }

      public Builder setSize(int value) {
        this.size = value;
        return this;
      }
    }
  }

  public static LocalReplicationControllers createCluster(LocalReplicationClusterSettings settings) {
    final List<LocalReplicationController> controllers = new ArrayList<>(settings.getSize());

    return new LocalReplicationControllersImpl(controllers);
  }

  public static final class ReplicatorEmulator {

  }
}
