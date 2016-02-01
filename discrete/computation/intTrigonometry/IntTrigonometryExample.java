

/**
 * Example of trigonometry based on integers.
 * Adapted from opensource UQM project (coded in C).
 *
 * @author Alexander Shabanov
 */
public final class IntTrigonometryExample {

  public static void main(String[] args) {
    demoTravel(0, 0, 100, 100, 20);
    demoTravel(0, 0, 100, -100, 20);
    demoTravel(0, 0, -100, 100, 20);
    demoTravel(0, 0, -100, -100, 20);

    demoTravel(0, 0, 100, 200, 20);
    demoTravel(0, 0, -100, -200, 20);
  }

  private static void demoTravel(int fromX, int fromY, int toX, int toY, int speed) {
    final int dx = toX - fromX;
    final int dy = toY - fromY;
    final int angle = arctan(dx, dy);

    final int newX = fromX + cosine(angle, speed);
    final int newY = fromY + sine(angle, speed);

    System.out.println("Travelling from [" + fromX + ", " + fromY + "] with V=" + speed +
        " to [" + toX + ", " + toY + "] " +
        ", dest=[" + newX + ", " + newY + "]");
  }

  //
  // Private
  //

  private static final int CIRCLE_SHIFT = 6;
  private static final int FULL_CIRCLE = (1 << CIRCLE_SHIFT);
  private static final int OCTANT_SHIFT = (CIRCLE_SHIFT - 3); // (1 << 3) == 8
  private static final int HALF_CIRCLE = (FULL_CIRCLE >> 1);
  private static final int QUADRANT = (FULL_CIRCLE >> 2);
  private static final int OCTANT = (FULL_CIRCLE >> 3);

  private static final int FACING_SHIFT = 4;

  private static final int SINE_SHIFT = 14;
  private static final int SINE_SCALE = (1 << SINE_SHIFT);

  // FLT_ADJUST
  private static int floatAdjust(double value) {
    return (int) (value * SINE_SCALE);
  }

  // NORMALIZE_ANGLE
  private static int normalizeAngle(int value) {
    return value & (FULL_CIRCLE - 1);
  }

  private static int normalizeFacing(int value) {
    return value & ((1 << FACING_SHIFT) - 1);
  }

  private static int degreesToAngle(int value) {
    return normalizeAngle(((value % 360) * FULL_CIRCLE + HALF_CIRCLE) / 360);
  }

  private static int anglesToDegree(int value) {
    throw new UnsupportedOperationException();
  }


  private static final int[] SINE_TAB = {
      -floatAdjust(1.000000),
      -floatAdjust(0.995185),
      -floatAdjust(0.980785),
      -floatAdjust(0.956940),
      -floatAdjust(0.923880),
      -floatAdjust(0.881921),
      -floatAdjust(0.831470),
      -floatAdjust(0.773010),
      -floatAdjust(0.707107),
      -floatAdjust(0.634393),
      -floatAdjust(0.555570),
      -floatAdjust(0.471397),
      -floatAdjust(0.382683),
      -floatAdjust(0.290285),
      -floatAdjust(0.195090),
      -floatAdjust(0.098017),
      floatAdjust(0.000000),
      floatAdjust(0.098017),
      floatAdjust(0.195090),
      floatAdjust(0.290285),
      floatAdjust(0.382683),
      floatAdjust(0.471397),
      floatAdjust(0.555570),
      floatAdjust(0.634393),
      floatAdjust(0.707107),
      floatAdjust(0.773010),
      floatAdjust(0.831470),
      floatAdjust(0.881921),
      floatAdjust(0.923880),
      floatAdjust(0.956940),
      floatAdjust(0.980785),
      floatAdjust(0.995185),
      floatAdjust(1.000000),
      floatAdjust(0.995185),
      floatAdjust(0.980785),
      floatAdjust(0.956940),
      floatAdjust(0.923880),
      floatAdjust(0.881921),
      floatAdjust(0.831470),
      floatAdjust(0.773010),
      floatAdjust(0.707107),
      floatAdjust(0.634393),
      floatAdjust(0.555570),
      floatAdjust(0.471397),
      floatAdjust(0.382683),
      floatAdjust(0.290285),
      floatAdjust(0.195090),
      floatAdjust(0.098017),
      floatAdjust(0.000000),
      -floatAdjust(0.098017),
      -floatAdjust(0.195090),
      -floatAdjust(0.290285),
      -floatAdjust(0.382683),
      -floatAdjust(0.471397),
      -floatAdjust(0.555570),
      -floatAdjust(0.634393),
      -floatAdjust(0.707107),
      -floatAdjust(0.773010),
      -floatAdjust(0.831470),
      -floatAdjust(0.881921),
      -floatAdjust(0.923880),
      -floatAdjust(0.956940),
      -floatAdjust(0.980785),
      -floatAdjust(0.995185),
  };

  private static final int[] ATAN_TAB = {
      0,
      0,
      1,
      1,
      1,
      2,
      2,
      2,
      2,
      3,
      3,
      3,
      4,
      4,
      4,
      4,
      5,
      5,
      5,
      5,
      6,
      6,
      6,
      6,
      7,
      7,
      7,
      7,
      7,
      7,
      8,
      8,
      8,
  };

  public static int sinVal(int angle) {
    return SINE_TAB[normalizeAngle(angle)];
  }

  public static int cosVal(int angle) {
    return sinVal(angle + QUADRANT);
  }

  public static int sine(int angle, int m) {
    return (sinVal(angle) * m) >> SINE_SHIFT;
  }

  public static int cosine(int angle, int m) {
    return sine(angle + QUADRANT, m);
  }

  public static int arctan(int deltaX, int deltaY) {
    int v1 = deltaX;
    int v2 = deltaY;
    if (v1 == 0 && v2 == 0) {
      return FULL_CIRCLE;
    }

    if (v1 < 0) {
      v1 = -v1;
    }
    if (v2 < 0) {
      v2 = -v2;
    }
    if (v1 > v2) {
      v1 = QUADRANT
          - ATAN_TAB[((v2 << (CIRCLE_SHIFT - 1)) + (v1 >> 1)) / v1];
    } else {
      v1 = ATAN_TAB[((v1 << (CIRCLE_SHIFT - 1)) + (v2 >> 1)) / v2];
    }

    if (deltaX < 0) {
      v1 = FULL_CIRCLE - v1;
    }

    if (deltaY > 0) {
      v1 = HALF_CIRCLE - v1;
    }

    return normalizeAngle(v1);
  }
}
