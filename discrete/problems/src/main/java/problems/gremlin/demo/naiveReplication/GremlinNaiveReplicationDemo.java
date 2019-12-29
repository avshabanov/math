package problems.gremlin.demo.naiveReplication;

import com.google.common.util.concurrent.Uninterruptibles;
import lombok.NonNull;
import lombok.val;
import problems.gremlin.GremlinAdapter;
import problems.gremlin.control.Decision;
import problems.gremlin.control.SingleDecisionProvider;
import problems.gremlin.demo.models.SimpleKeyValueStore;
import problems.gremlin.demo.models.SimpleKeyValueStoreBase;

import java.util.concurrent.TimeUnit;

/**
 * A demo, showing consistency issues with naive replication.
 */
public class GremlinNaiveReplicationDemo {

  public static final class Demo1 {
    public static void main(String[] args) {
      final SingleDecisionProvider decisionProvider1 = new SingleDecisionProvider();
      final Participant participant1 = GremlinAdapter.create(
          new ParticipantImpl(new SimpleKeyValueStoreBase()),
          Participant.class,
          decisionProvider1
      );

      final SingleDecisionProvider decisionProvider2 = new SingleDecisionProvider();
      decisionProvider2.setDecision(Decision.builder().delayBeforeMillis(20L).delayAfterMillis(10L).build());
      final Participant participant2 = GremlinAdapter.create(
          new ParticipantImpl(new SimpleKeyValueStoreBase()),
          Participant.class,
          decisionProvider2
      );

      // make participants know each other
      participant1.setPeer(participant2);
      participant2.setPeer(participant1);

      // normal flow
      participant1.put("1", "one");
      System.out.println("[T+0] participant2.get(1)=" + participant2.get("1"));
      //noinspection UnstableApiUsage
      Uninterruptibles.sleepUninterruptibly(100L, TimeUnit.MILLISECONDS);

      System.out.println("[T+1] participant2.get(1)=" + participant2.get("1"));

      System.exit(0);
    }
  }

  public interface Participant extends SimpleKeyValueStore {
    void setPeer(@NonNull Participant other);
  }

  public static final class ParticipantImpl implements Participant {
    private final SimpleKeyValueStore backingStore;
    private Participant peer;

    ParticipantImpl(@NonNull SimpleKeyValueStore backingStore) {
      this.backingStore = backingStore;
    }

    @Override
    public void put(@NonNull String key, @NonNull String value) {
      val t = new Thread(() -> this.peer.put(key, value));
      t.start();
      this.backingStore.put(key, value);
    }

    @Override
    public String get(@NonNull String key) {
      return backingStore.get(key);
    }

    @Override
    public void setPeer(@NonNull Participant other) {
      peer = other;
    }
  }
}
