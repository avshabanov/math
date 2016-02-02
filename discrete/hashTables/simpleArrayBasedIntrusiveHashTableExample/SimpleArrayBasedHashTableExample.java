import support.SimpleIntrusiveHashMap;
import support.IntrusiveHashMap;

/**
 * Illustration of simple, array-based hash table implementation (ideal for immutable hash tables).
 *
 * @author Alexander Shabanov
 */
public class SimpleArrayBasedHashTableExample {

  public static void main(String[] args) {
    final IntrusiveHashMap<Integer, Integer> intSet = SimpleIntrusiveHashMap.createSet();
    intSet.add(1);
    intSet.add(2);

    System.out.println("intSet=" + intSet);

    final IntrusiveHashMap<String, Person> personMap = SimpleIntrusiveHashMap.createMap((person) -> person.name);
    personMap.add(new Person("alice", 19));
    personMap.add(new Person("bob", 37));
    personMap.add(new Person("dave", 42));
    personMap.add(new Person("dave", 35)); // will override previous 'Dave'
    personMap.add(new Person("eva", 28));

    System.out.println("personMap=" + personMap);

    System.out.println("Dave from personMap=" + personMap.getByKey("dave"));

    // more sofisticated example - use remove operation + initial capacity and load factor
    final IntrusiveHashMap<String, String> strSet = SimpleIntrusiveHashMap.createSet(5, 0.99f);
    strSet.add("A");
    strSet.add("B");
    strSet.add("C");
    strSet.add("D");
    strSet.remove("B");
    System.out.println("strSet=" + strSet);
  }

  private static final class Person {
    final String name; // name is a key
    final int age;

    public Person(String name, int age) {
      this.name = name;
      this.age = age;
    }

    @Override
    public String toString() {
      return '{' + name + ", age " + age + '}';
    }
  }
}
