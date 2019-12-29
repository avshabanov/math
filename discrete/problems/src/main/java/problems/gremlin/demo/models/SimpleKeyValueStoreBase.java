package problems.gremlin.demo.models;

import java.util.concurrent.ConcurrentHashMap;

public class SimpleKeyValueStoreBase implements SimpleKeyValueStore {
  private final ConcurrentHashMap<String, String> map = new ConcurrentHashMap<>();

  @Override
  public void put(String key, String value) {
    map.put(key, value);
  }

  @Override
  public String get(String key) {
    return map.get(key);
  }
}
