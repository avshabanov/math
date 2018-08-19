import java.util.*;

/**
 * Given an array nums of n integers, are there elements a, b, c in nums such that a + b + c = 0?
 * Find all unique triplets in the array which gives the sum of zero.
 * Note:
 * The solution set must not contain duplicate triplets.
 * See https://leetcode.com/problems/3sum/description/
 */
class Solution {
    public List<List<Integer>> threeSum(int[] nums) {
        final List<List<Integer>> result = new ArrayList<>();
        Arrays.sort(nums);
        
        for (int i0 = 0; i0 < nums.length; ++i0) {
            final int a = nums[i0];
            if ((i0 > 0) && (nums[i0 - 1] == a)) {
                continue;
            }
            
            if (a > 0) {
                break;
            }
            
            final int i1Start = i0 + 1;
            for (int i1 = i1Start; i1 < nums.length; ++i1) {
                final int b = nums[i1];
                if ((i1 > i1Start) && (nums[i1 - 1] == b)) {
                    continue;
                }
                
                if ((a + b) > 0) {
                    break;
                }
                
                final int i2Start = i1 + 1;
                for (int i2 = i2Start; i2 < nums.length; ++i2) {
                    final int c = nums[i2];
                    if ((i2 > i2Start) && (nums[i2 - 1] == c)) {
                        continue;
                    }
                    
                    final int sum = a + b + c;
                    if (sum > 0) {
                        break;
                    }
                    
                    if (sum == 0) {
                        result.add(Arrays.<Integer>asList(a, b, c));
                    }
                }
            }
        }
        return result;
    }
}

