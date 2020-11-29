package simplecalc2

import "testing"

func TestCalc(t *testing.T) {
	t.Logf("result=%d", calculate("14/3*2"))
	t.Logf("result=%d", calculate("2*2 + 3*3 + 4*4"))
	t.Logf("result=%d", calculate("1+2*3*2"))
	t.Logf("result=%d", calculate("1+2*3"))
}

/*
Easier approach:

func calculate(s string) int {

    nums := make([]int, 0)
    curNum := 0
    prevOp := '+'
    s = s + "+"

    for i := 0; i < len(s); i++ {
        if s[i] >= '0' && s[i] <= '9' {
            curNum = curNum * 10 + int(s[i] - '0')
        } else if s[i] == ' ' {
            continue
        } else {
            if prevOp == '+' {
                nums = append(nums, curNum)
            } else if prevOp == '-' {
                nums = append(nums, -1 * curNum)
            } else if prevOp == '*' {
                nums[len(nums)-1] = nums[len(nums) - 1] * curNum
            } else if prevOp == '/' {
                nums[len(nums)-1]  =nums[len(nums) - 1] / curNum
            }
            prevOp = rune(s[i])
            curNum = 0
        }
    }

    sum := 0
    for _, num := range(nums) {
        sum += num
    }

    return sum

}
*/
