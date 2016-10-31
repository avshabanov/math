package com.alexshabanov.simulation.replication.sample.dao.support;

import com.alexshabanov.simulation.replication.sample.dao.UserDao;
import com.alexshabanov.simulation.replication.sample.model.User;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.List;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ThreadLocalRandom;
import java.util.stream.Collectors;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public final class DefaultUserDao implements UserDao{

  private final ConcurrentHashMap<String, User> data = new ConcurrentHashMap<>();

  @Override
  public String create(String name, int age) {
    final String id = Long.toHexString(ThreadLocalRandom.current().nextLong(Long.MAX_VALUE));
    final User user = new User();
    user.id = id;
    user.name = name;
    user.age = age;
    data.put(id, user);
    return id;
  }

  @Override
  public void update(String id, @Nullable String name, @Nullable Integer age) {
    final User user = data.get(id);
    if (user == null) {
      throw new IllegalArgumentException("Unknown id=" + id);
    }

    if (name != null) {
      user.name = name;
    }

    if (age != null) {
      user.age = age;
    }
  }

  @Override
  public User get(String id) {
    final User user = data.get(id);
    if (user == null) {
      throw new IllegalArgumentException("Non-existent id=" + id);
    }

    return user.copy();
  }

  @Override
  public List<User> getAll() {
    return data.values().stream().map(User::copy).collect(Collectors.toList());
  }

  @Override
  public void delete(String id) {
    data.remove(id);
  }
}
