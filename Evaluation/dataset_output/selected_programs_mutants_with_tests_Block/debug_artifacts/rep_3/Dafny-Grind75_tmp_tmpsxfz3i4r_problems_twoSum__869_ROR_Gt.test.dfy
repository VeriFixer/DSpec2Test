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

method {:test} Test6() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 0, 0, 0, 24130, 2437, 0, 5, 9];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 26567) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 26567), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 26567);
}
method {:test} Test7() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 2437, 24130];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 26567) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 26567), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 26567);
}
method {:test} Test8() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 15916, 1796];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 17712) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 17712), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 17712);
}

// REPEAT 3 - TIME: 7.2307782 s
