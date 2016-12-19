package com.alexshabanov.simulation.replication;

import com.alexshabanov.simulation.replication.v1.logic.dummy.DummyReplicator;
import com.alexshabanov.simulation.replication.v1.sample.dao.UserDao;
import com.alexshabanov.simulation.replication.v1.sample.dao.support.DefaultUserDao;
import com.alexshabanov.simulation.replication.v1.sample.dao.support.ReplicatedUserDao;
import com.alexshabanov.simulation.replication.v1.sample.model.User;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * @author Alexander Shabanov
 */
public final class DummyReplicatorTest {
  private UserDao userDao;
  private AutoCloseable closeable;

  @Before
  public void init() {
    final UserDao localDao = new DefaultUserDao();
    final ReplicatedUserDao replicatedUserDao = new ReplicatedUserDao(localDao, DummyReplicator.INSTANCE);
    this.userDao = replicatedUserDao;
    this.closeable = replicatedUserDao;
  }

  @After
  public void cleanup() throws Exception {
    closeable.close();
  }

  @Test
  public void shouldPersistUsers() {
    // Given:
    final String username = "username";

    // When:
    final String id = userDao.create(username, 20);

    // Then:
    final User user = userDao.get(id);
    assertEquals(username, user.name);
  }
}
