package com.alexshabanov.simulation.replication.v1.sample.dao.support;

import com.alexshabanov.simulation.replication.v1.logic.ReplicatedOperation;
import com.alexshabanov.simulation.replication.v1.logic.ReplicationListener;
import com.alexshabanov.simulation.replication.v1.logic.Replicator;
import com.alexshabanov.simulation.replication.v1.logic.SubscriptionResult;
import com.alexshabanov.simulation.replication.v1.sample.dao.UserDao;
import com.alexshabanov.simulation.replication.v1.sample.model.User;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.io.Serializable;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public final class ReplicatedUserDao implements UserDao, ReplicationListener, AutoCloseable {
  public static final String ENTITY_TYPE = "User";

  private final UserDao delegate;

  private final Replicator replicator; // TODO: decouple replication from local DAO
  private volatile SubscriptionResult subscriptionResult;

  public ReplicatedUserDao(UserDao delegate, Replicator replicator) {
    this.delegate = delegate;
    this.replicator = replicator;
    this.subscriptionResult = replicator.subscribe(ENTITY_TYPE, this);
  }

  @Override
  public String create(String name, int age) {
    final String id = delegate.create(name, age);
    // TODO: transactional behavior required here: rollback if replication failed
    replicator.replicate(ReplicatedOperation.CREATE, ENTITY_TYPE, ReplicationCreateUser.create(id, name, age));
    return id;
  }

  @Override
  public void update(String id, @Nullable String name, @Nullable Integer age) {
    delegate.update(id, name, age);
  }

  @Override
  public User get(String id) {
    return delegate.get(id);
  }

  @Override
  public List<User> getAll() {
    return delegate.getAll();
  }

  @Override
  public void delete(String id) {
    delegate.delete(id);
  }

  @Override
  public void applyReplicatedValue(ReplicatedOperation operation, Object value) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void close() throws Exception {
    if (subscriptionResult != null) {
      subscriptionResult.unsubscibe();
      subscriptionResult = null;
    }
  }

  //
  // Private
  //

  private static final class ReplicationCreateUser implements Serializable {

    private static final long serialVersionUID = 1L;

    String id;
    String name;
    int age;

    static ReplicationCreateUser create(String id, String name, int age) {
      final ReplicationCreateUser result = new ReplicationCreateUser();
      result.id = id;
      result.name = name;
      result.age = age;
      return result;
    }
  }
}
