package com.alexshabanov.simulation.replication.v1.sample.dao;

import com.alexshabanov.simulation.replication.v1.sample.model.User;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.List;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public interface UserDao {

  String create(String name, int age);

  void update(String id, @Nullable String name, @Nullable Integer age);

  User get(String id);

  List<User> getAll();

  void delete(String id);
}
