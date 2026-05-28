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
  while i < n - 1
    invariant 0 <= i < j <= n
    invariant forall ii, jj :: 0 <= ii < i && ii < jj < n ==> nums[ii] + nums[jj] != target
  {
    break;
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
var seqint0 : seq<int> := [1797, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, -1796];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 0);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 0;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 0;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [1797, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1796, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| > 1, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i, j :: 0 <= i < j < |seqint0| && seqint0[i] + seqint0[j] == 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := twoSum(seqint0, 0);
expect 0 <= r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 0;
expect forall ii, jj :: 0 <= ii < r0 && ii < jj < |seqint0| ==> seqint0[ii] + seqint0[jj] != 0;
expect forall jj :: r0 < jj < r1 ==> seqint0[r0] + seqint0[jj] != 0;
}
