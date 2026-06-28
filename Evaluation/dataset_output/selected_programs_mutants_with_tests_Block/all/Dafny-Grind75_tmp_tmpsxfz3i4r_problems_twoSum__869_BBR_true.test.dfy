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
  while true
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


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8855, -7059];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 1796) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 1796), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 1796);
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059, 1796];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8855) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8855), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8855);
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 5853, -5244, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 609) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 609), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 609);
}

// REPEAT 1 - TIME: 3.3125772 s

method {:test} Test3() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15274, 2437, 4];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 17711) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 17711), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 17711);
}
method {:test} Test4() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8855, 4];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8856) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8856), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8856);
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 8855, 1, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 4, 0, 8];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8856) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8856), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8856);
}

// REPEAT 2 - TIME: 5.4015199 s

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

method {:test} Test9() {
var seqint0 : seq<int> := [7, 0, 2437, 32986];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 35423) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 35423), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 35423);
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 8365, 20485, 0, 0, 12, 0, 0, 7, 0, 0, 14, 0, 0, 16, 18];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 28850) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 28850), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 28850);
}
method {:test} Test11() {
var seqint0 : seq<int> := [7, 0, 0, 1142, 25426, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 26568) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 26568), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 26568);
}

// REPEAT 4 - TIME: 9.370259 s

method {:test} Test12() {
var seqint0 : seq<int> := [10, 7719, 28941];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 36660) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 36660), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 36660);
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 2437, 41842, 0, 0, 0, 0, 15, 10];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 44279) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 44279), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 44279);
}
method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 41842, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 44279) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 44279), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 44279);
}

// REPEAT 5 - TIME: 11.4628427 s

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

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 59064, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 61501) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 61501), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 61501);
}
method {:test} Test20() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8855, 45587, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 54442) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 54442), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 54442);
}

// REPEAT 7 - TIME: 15.1149922 s

method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 1796, 68071, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 69867) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 69867), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 69867);
}
method {:test} Test22() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 67920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 70357) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 70357), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 70357);
}
method {:test} Test23() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 8855, 54443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 63298) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 63298), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 63298);
}

// REPEAT 8 - TIME: 17.4576841 s

method {:test} Test24() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 76776, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 79213) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 79213), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 79213);
}
method {:test} Test25() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8855, 63299, 0, 0, 0, 0, 0, 0, 20, 0, 24, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 72154) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 72154), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 72154);
}

// REPEAT 9 - TIME: 19.9075835 s

method {:test} Test27() {
var seqint0 : seq<int> := [0, 72645, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 81010) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 81010), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 81010);
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 449, 79374, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 79823) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 79823), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 79823);
}

// REPEAT 10 - TIME: 22.58215 s
