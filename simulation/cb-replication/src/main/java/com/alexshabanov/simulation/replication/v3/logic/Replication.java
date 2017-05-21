package com.alexshabanov.simulation.replication.v3.logic;

import java.io.IOException;
import java.io.InputStream;

public final class Replication {

  public interface Changeset {

  }

  public interface ReplicatedEntitySerializer {
    void write(InputStream inputStream) throws IOException;
  }

  public interface ReplicationActionSettings {
  }

  public enum StandardReplicationActionSettings implements ReplicationActionSettings {
    DEFAULT
  }

  public interface Replicator {

    void replicate(
        ReplicatedEntitySerializer serializer,
        ReplicationActionSettings settings);

    default void replicate(ReplicatedEntitySerializer serializer) {
      replicate(serializer, StandardReplicationActionSettings.DEFAULT);
    }
  }

  public interface ReplicatedEntity {

    byte[] getBytes();
    int getBytesOffset();
    int getBytesLength();
  }

  public interface ReplicationCallback {

    void applyReplicatedEntity(ReplicatedEntity entity);
  }

  public static void test() {
  }
}
