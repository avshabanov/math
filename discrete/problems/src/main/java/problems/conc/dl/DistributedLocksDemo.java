package problems.conc.dl;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import lombok.Builder;
import lombok.NonNull;
import lombok.Value;
import lombok.val;

import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Sample demo for distributed locks
 */
public class DistributedLocksDemo {

  /**
   * Lock server protocol.
   *
   * <br/>
   * <strong>Master:</strong>
   * The master must obtain votes from a majority of replicas that promise to not elect a different master
   * for an interval of a few seconds (which is a **master lease**)
   * <br/>
   * Quorum=2 for N=3
   * Master: maintain copies of a simple DB with replicas
   */
  interface LockServer {
    // master
    String get(String key);
    void put(String key, String value);
  }

  @Value
  @Builder
  static class WriteRequest {
    long id;
    String origin; // origin+id together form a vector clock
    byte[] payload;
  }

  interface ConsensusParticipant {

    void acceptMasterHeartbeat(@NonNull String masterNodeId);
    @NonNull MasterElectionResult prepareForMaster(@NonNull String masterNodeId, long timeMillis);
    @NonNull String getNodeId();
    void acceptWriteRequest(@NonNull WriteRequest request);

    enum State {
      UNDECIDED,
      MASTER,
      REPLICA
    }

    @Value
    @Builder
    class MasterElectionResult {
      boolean accepted;
      String existingMasterId;
    }
  }

  interface ParticipantFinder<T> {
    List<T> scanParticipants();
  }

  static final class Cluster<T> implements ParticipantFinder<T> {
    private final List<T> participants = new CopyOnWriteArrayList<>();

    @Override
    public List<T> scanParticipants() {
      return ImmutableList.copyOf(participants);
    }
  }

  interface LockServerNode extends LockServer, ConsensusParticipant {
  }

  static final class LockServerImpl implements LockServerNode {

    private final String nodeId = String.format("node-%s", UUID.randomUUID());
    private final AtomicLong replicationLogCounter = new AtomicLong(); // for write request logs
    private final Map<String, String> store = new ConcurrentHashMap<>();
    private final List<WriteRequest> replicationLog = new CopyOnWriteArrayList<>();
    private volatile long masterPrepareConfirmationTimeMillis;
    private volatile LifecycleState lifecycleState = LifecycleState.UNKNOWN;
    private volatile long lastMasterHeartbeatTimeMillis;
    private volatile LockServerNode master;
    private volatile List<LockServerNode> participants;
    private volatile int majority;
    private final ParticipantFinder<LockServerNode> participantFinder;

    public LockServerImpl(@NonNull ParticipantFinder<LockServerNode> participantFinder) {
      this.participantFinder = participantFinder;
    }

    @Override
    public String get(String key) {
      switch (lifecycleState) {
        case MASTER:
          // I'm a master, I can serve the reads myself
          return store.get(key);

        case REPLICA:
          // I'm a replica, but I know who master is; redirect request to the master node;
          // in HTTP world this would be a plain and simple redirect
          return master.get(key);

        default:
          // I'm not yet initialized; I can't serve read requests
          throw new IllegalStateException("Node " + nodeId + " has not been initialized yet; please retry your request");
      }
    }

    @Override
    public void put(String key, String value) {
      switch (lifecycleState) {
        case MASTER:
          // I'm a master, it is ok to serve this
          final String serializedString = "v1;" + key + ";" + value;
          final WriteRequest writeRequest = WriteRequest.builder()
              .payload(serializedString.getBytes(StandardCharsets.UTF_8))
              .id(replicationLogCounter.incrementAndGet())
              .origin(nodeId)
              .build();
          // need to reach majority: these could be done in parallel
          int accepted = 0;
          for (LockServerNode replicas : participants) {
            try {
              replicas.acceptWriteRequest(writeRequest);
              ++accepted;
            } catch (Exception e) {
              // service is unavailable or response lost in transit, etc.
              // TODO: log error?
            }
          }

          // write replica-confirmed write request
          replicationLog.add(writeRequest);

          if (accepted < majority) {
            // we can't accept this write request even though we logged it; another retry needs to happen
            throw new RuntimeException("Retry needed: insufficient quorum");
          }

          // at this point of time we have the majority, so accept the written value
          store.put(key, value);
          return;

        case REPLICA:
          // I'm a replica, but I know who master is, so send request there
          master.put(key, value);
          return;

        default:
          // I'm not a master node; it should go somewhere else
          throw new IllegalStateException("Node=" + nodeId + " has not been initialized yet; please retry your request");
      }

    }

    @Override public void acceptMasterHeartbeat(@NonNull String masterNodeId) {
      if (lifecycleState != LifecycleState.REPLICA) {
        throw new IllegalStateException("Node=" + nodeId + " has lifecycleState=" + lifecycleState +
            "; can't accept master heartbeat");
      }

      if (!masterNodeId.equals(master.getNodeId())) {
        throw new IllegalStateException("Node=" + nodeId + " is not a replica of =" + masterNodeId +
            "; can't accept master heartbeat; intended master is " + master.getNodeId());
      }

      // ok; heartbeat accepted
      lastMasterHeartbeatTimeMillis = System.currentTimeMillis();
    }

    @Override public @NonNull MasterElectionResult prepareForMaster(String masterNodeId, long timeMillis) {
      if (lifecycleState == LifecycleState.REPLICA) {
        if (masterNodeId.equals(master.getNodeId())) {
          // extend the time and return
          masterPrepareConfirmationTimeMillis = System.currentTimeMillis() + timeMillis;
          return MasterElectionResult.builder().accepted(true).build();
        }
        return MasterElectionResult.builder().accepted(false).existingMasterId(master.getNodeId()).build();
      } else if (lifecycleState != LifecycleState.UNKNOWN) {
        throw new IllegalStateException("Node=" + nodeId + " can't prepare for master; " +
            "its lifecycle state is " + lifecycleState);
      }

      if (masterPrepareConfirmationTimeMillis > System.currentTimeMillis()) {
        throw new IllegalStateException("Node=" + nodeId + " can't prepare for master; " +
            "it has promised to prepare for master for other node");
      }

      // ok: at this time we can prepare this node as a replica
      final List<LockServerNode> participants = participantFinder.scanParticipants();
      LockServerNode masterCandidate = null;
      for (final LockServerNode n : participants) {
        if (n.getNodeId().equals(masterNodeId)) {
          if (masterCandidate != null) {
            throw new RuntimeException("Catastrophic failure: duplicate master nodes");
          }
          masterCandidate = n;
        }
      }

      if (masterCandidate == null) {
        throw new RuntimeException("Unable to find master node for " + masterNodeId);
      }

      // update the state with the found master
      master = masterCandidate;
      lifecycleState = LifecycleState.REPLICA;
      masterPrepareConfirmationTimeMillis = timeMillis;

      return MasterElectionResult.builder().accepted(true).build();
    }

    @Override public @NonNull String getNodeId() {
      return nodeId;
    }

    @Override public void acceptWriteRequest(@NonNull WriteRequest request) {
      if (lifecycleState != LifecycleState.REPLICA) {
        throw new IllegalStateException("Node=" + nodeId + " is not a replica, ignoring write request=" + request);
      }

      if (!request.getOrigin().equals(master.getNodeId())) {
        throw new IllegalStateException("Node=" + nodeId + " got unexpected write request=" + request +
            " from non-elected master; current master=" + master.getNodeId());
      }

      replicationLog.add(request);
    }

    enum LifecycleState {
      UNKNOWN,
      MASTER,
      REPLICA,
      COOLDOWN
    }
  }


  public static final class Demo1 {
    public static void main(String[] args) {
      System.out.println("demo");
    }
  }
}
