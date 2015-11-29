package projectScheduleDemoSupport;

/**
 * @author Alexander Shabanov
 */
public final class ResourceUnits {
  private final Resource resource;
  private final int units;

  public ResourceUnits(Resource resource, int units) {
    this.resource = resource;
    this.units = units;
  }

  public Resource getResource() {
    return resource;
  }

  public int getUnits() {
    return units;
  }
}
