// Dafny-Grind75_tmp_tmpsxfz3i4r_problems_twoSum.dfy

predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
  requires i < |nums|
  requires j < |nums|
{
  i != j &&
  nums[i] + nums[j] == target
}

method {:testEntry} twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
  requires exists i: nat, j: nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l < m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
  ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
  pair := (0, 0);
  var i: nat := 0;
  while i > |nums|
    invariant i <= |nums|
    invariant forall z: nat, j: nat :: 0 <= z < i && z + 1 <= j < |nums| ==> !summingPair(z, j, nums, target)
  {
    var k: nat := i + 1;
    while k < |nums|
      invariant i + 1 <= k <= |nums|
      invariant forall q: nat :: i + 1 <= q < k <= |nums| ==> !summingPair(i, q, nums, target)
    {
      if nums[i] + nums[k] == target {
        pair := (i, k);
        return pair;
      }
      k := k + 1;
    }
    i := i + 1;
  }
}

method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 37217, 13, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 25, 23];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 39013) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 39013), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 39013);
}
method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 24565, 0, 0, 0, 0, 0, 13, 0, 20, 0, 0, 0, 23, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 32930) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 32930), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 32930);
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 30488, 0, 0, 609];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 31097) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 31097), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 31097);
}

// REPEAT 6 - TIME: 13.0670611 s
