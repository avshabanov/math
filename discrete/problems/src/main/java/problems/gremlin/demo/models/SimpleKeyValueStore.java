package problems.gremlin.demo.models;

import lombok.NonNull;

public interface SimpleKeyValueStore {

  void put(@NonNull String key, @NonNull String value);

  String get(@NonNull String key);
}
