// Clover_two_sum.dfy

method {:testEntry} twoSum(nums: seq<int>, target: int)
    returns (i: int, j: int)
  requires |nums| > 1
  requires exists i, j :: 0 <= i < j < |nums| && nums[i] + nums[j] == target
  ensures 0 <= i < j < |nums| && nums[i] + nums[j] == target
  ensures forall ii, jj :: 0 <= ii < i && ii < jj < |nums| ==> nums[ii] + nums[jj] != target
  ensures forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
{
  var n := |nums|;
  i := 0;
  j := 1;
  while i >= n - 1
    invariant 0 <= i < j <= n
    invariant forall ii, jj :: 0 <= ii < i && ii < jj < n ==> nums[ii] + nums[jj] != target
  {
    j := i + 1;
    while j < n
      invariant 0 <= i < j <= n
      invariant forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
    {
      if nums[i] + nums[j] == target {
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 2998, 3000, 2998, 2999, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2997, 2996];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 5996, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 5996);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 5996;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 5996;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 5996;
}
method {:test} Test1() {
var seqint0 : seq<int> := [5836, 161, 0, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5837, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4616, 1381];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 5997, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 5997);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 5997;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 5997;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 5997;
}
method {:test} Test2() {
var seqint0 : seq<int> := [7424, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 858, 7424, 6858, 1424, 0, 0, 1422];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 8282, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 8282);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 8282;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 8282;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 8282;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 10991, -1637, 1244, 0, 0, 10990, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2711, -1636, -1635, 6643];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 9354, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 9354);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 9354;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 9354;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 9354;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10625, 16621, 10625, 0, 0, 0, 16621, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 27246, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 27246);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 27246;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 27246;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 27246;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 22173, 13173, 22052, 13172, 0, 0, 22171, 13174, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13172, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i: int, j: int {:trigger seqint0[j], seqint0[i]} :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 35345, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 35345);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 35345;
expect forall ii: int, jj: int {:trigger seqint0[jj], seqint0[ii]} :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 35345;
expect forall jj: int {:trigger seqint0[jj]} :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 35345;
}
