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
  while i < |nums|
    invariant i <= |nums|
    invariant forall z: nat, j: nat :: 0 <= z < i && z + 1 <= j < |nums| ==> !summingPair(z, j, nums, target)
  {
    break;
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

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 2282, 18162, 0, 0, 0, 15, 0, 0, 7, 0, 0, 0, 0, 17, 11];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 20444) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 20444), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 20444);
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 18199, 1796, 0, 7, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 19995) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 19995), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 19995);
}
method {:test} Test11() {
var seqint0 : seq<int> := [7, 449, 0, 0, 0, 28401, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 28850) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 28850), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 28850);
}

// REPEAT 4 - TIME: 9.2076166 s
