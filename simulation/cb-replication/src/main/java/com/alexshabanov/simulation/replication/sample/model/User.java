package com.alexshabanov.simulation.replication.sample.model;

import javax.annotation.ParametersAreNonnullByDefault;

/**
 * @author Alexander Shabanov
 */
@ParametersAreNonnullByDefault
public class User {
  public String id;
  public String name;
  public int age;

  public User copy() {
    final User result = new User();
    result.id = this.id;
    result.name = this.name;
    result.age = this.age;
    return result;
  }
}
