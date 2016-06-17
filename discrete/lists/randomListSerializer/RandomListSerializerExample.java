import support.SingleLinkedListSupport;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Sample run:
 * <pre>
 * Serializing rnodes=[1]
 * 	Deserialized=[1]
 * Serializing rnodes=[1, 2->(1)]
 * 	Deserialized=[1, 2->(1)]
 * Serializing rnodes=[1->(2), 2->(1), 2]
 * 	Deserialized=[1->(2), 2->(1), 2]
 * </pre>
 *
 * @author Alexander Shabanov
 */
public final class RandomListSerializerExample extends SingleLinkedListSupport {

  public static void main(String[] args) {
    {
      RNode r1 = new RNode();
      r1.setValue("1");
      demo(r1);
    }

    {
      RNode r1 = new RNode();
      r1.setValue("1");
      RNode r2 = new RNode();
      r2.setValue("2");
      r1.setNext(r2);
      r2.setRandNode(r1);
      demo(r1);
    }

    {
      RNode r1 = new RNode();
      r1.setValue("1");
      RNode r2 = new RNode();
      r2.setValue("2");
      r1.setNext(r2);
      r2.setRandNode(r1);
      RNode r3 = new RNode();
      r2.setNext(r3);
      r3.setValue("2");
      r1.setRandNode(r3);
      demo(r1);
    }
  }

  private static void demo(RNode rnodes) {
    System.out.println("Serializing rnodes=" + rnodes);
    final byte[] b = serialize(rnodes);
    final RNode deserialized = deserialize(b);
    System.out.println("\tDeserialized=" + deserialized);
  }

  private static byte[] serialize(RNode rn) {
    final List<RFwd> fwd = new ArrayList<>();
    final Map<RNode, Integer> indexes = new HashMap<>();

    serializeNode(rn, indexes, fwd);

    try (final ByteArrayOutputStream baos = new ByteArrayOutputStream()) {
      try (final ObjectOutputStream oos = new ObjectOutputStream(baos)) {
        oos.writeObject(fwd);
      }
      return baos.toByteArray();
    } catch (IOException e) {
      throw new IllegalStateException(e);
    }
  }

  private static int serializeNode(RNode rn, Map<RNode, Integer> indexes, List<RFwd> fwd) {
    if (rn == null) {
      return -1;
    }

    Integer idx = indexes.get(rn);
    if (idx == null) {
      // new entry
      final RFwd rFwd = new RFwd();

      idx = fwd.size();
      fwd.add(rFwd);
      indexes.put(rn, idx);

      rFwd.value = rn.getValue();
      rFwd.nextIndex = serializeNode((RNode) rn.getNext(), indexes, fwd);
      rFwd.randIndex = serializeNode(rn.getRandNode(), indexes, fwd);
    }

    return idx;
  }

  private static RNode deserialize(byte[] values) {
    List<RFwd> rFwds;
    try (final ByteArrayInputStream bais = new ByteArrayInputStream(values)) {
      try (final ObjectInputStream ois = new ObjectInputStream(bais)) {
        //noinspection unchecked
        rFwds = (List<RFwd>) ois.readObject();
      } catch (ClassNotFoundException e) {
        throw new IllegalStateException(e);
      }
    } catch (IOException e) {
      throw new IllegalStateException(e);
    }

    final List<RNode> rnodes = rFwds.stream().map(x -> ((RNode) null)).collect(Collectors.toList());
    return deserialize(rnodes.isEmpty() ? -1 : 0, rFwds, rnodes);
  }

  private static RNode deserialize(int index, List<RFwd> rFwds, List<RNode> rnodes) {
    if (index == -1) {
      return null;
    }
    RNode result = rnodes.get(index);
    if (result == null) {
      result = new RNode();
      RFwd rFwd = rFwds.get(index);
      rnodes.set(index, result);
      result.setValue(rFwd.value);

      result.setNext(deserialize(rFwd.nextIndex, rFwds, rnodes));
      result.setRandNode(deserialize(rFwd.randIndex, rFwds, rnodes));
    }
    return result;
  }

  private static final class RFwd implements Serializable {
    private static final long serialVersionUID = 1;
    int nextIndex;
    int randIndex;
    String value;
  }

  private static final class RNode extends Node<String> {
    private final Object id = new Object();
    private RNode randNode;

    public RNode getRandNode() {
      return randNode;
    }

    public void setRandNode(RNode randNode) {
      this.randNode = randNode;
    }

    @Override
    protected void stringifyNode(StringBuilder target) {
      target.append(getValue());
      if (getRandNode() != null) {
        target.append("->(").append(getRandNode().getValue()).append(')');
      }
    }

    @Override
    public boolean equals(Object o) {
      if (o instanceof RNode) {
        return id.equals(((RNode) o).id);
      }
      return false;
    }

    @Override
    public int hashCode() {
      return id.hashCode();
    }
  }
}
