/**
 * Top-left edge should be White-Cyan-Blue with White on top, Cyan to the left and Red to the rear side.
 * In this case Orange on the front side and Yellow is on the bottom.
 *
 *    [0]
 * [1][2][3]
 *    [4]
 *    [5]
 */
public final class OptRubikSample {

  private static final class Solution2x2 {
    static final int CL_ORANGE = 0;
    static final int CL_YELLOW = 1;
    static final int CL_GREEN = 2;
    static final int CL_WHITE = 3;
    static final int CL_RED = 4;
    static final int CL_CYAN = 5;

    // edges as they appear in top-left position of the cube (top-left-rear)
    static final int[] EDGES = {
        CL_WHITE + CL_CYAN >> 3 + CL_RED >> 6,
        CL_CYAN + CL_YELLOW >> 3 + CL_RED >> 6,
        CL_CYAN + CL_WHITE >> 3 + CL_ORANGE >> 6,
        CL_ORANGE + CL_GREEN >> 3 + CL_YELLOW >> 6,
        CL_GREEN + CL_RED >> 3 + CL_YELLOW >> 6,
        CL_YELLOW + CL_CYAN >> 3 + CL_ORANGE >> 6,
        CL_GREEN + CL_ORANGE >> 3 + CL_WHITE >> 6,
        CL_GREEN + CL_WHITE >> 3 + CL_RED >> 6,
    };
  }
}
