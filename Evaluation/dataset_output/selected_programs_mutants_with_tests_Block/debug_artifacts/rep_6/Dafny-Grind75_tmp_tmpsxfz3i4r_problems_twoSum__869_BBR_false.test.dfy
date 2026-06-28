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
  while false
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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 19, 8365, 38197, 0, 21];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 46562) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 46562), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 46562);
}
method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 50849, 21];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 52645) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 52645), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 52645);
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 50849, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 52645) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 52645), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 52645);
}

// REPEAT 6 - TIME: 13.146062 s
