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
    var k: nat := i;
    while k < |nums|
      invariant i + 1 <= k <= |nums|
      invariant forall q: nat :: i + 1 <= q < k <= |nums| ==> !summingPair(i, q, nums, target)
    {
      if nums[i] == target {
        pair := (i, k);
        return pair;
      }
      k := k;
    }
    i := i;
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

// REPEAT 1 - TIME: 3.4065067 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 7719, 2373];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 10092) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 10092), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 10092);
}
method {:test} Test4() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8855, 4];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8856) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8856), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8856);
}
method {:test} Test5() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 8365, 2773];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 11138) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 11138), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 11138);
}

// REPEAT 2 - TIME: 5.3662452 s

method {:test} Test6() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 17557, 2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 19994) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 19994), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 19994);
}
method {:test} Test7() {
var seqint0 : seq<int> := [0, 4080, 8855, 0, 0, 0, 0, 0, 0, 0, 0, 8, 10, 12, 0, 5, 0, 0, 0, 0, 0, 14];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 12935) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 12935), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 12935);
}
method {:test} Test8() {
var seqint0 : seq<int> := [5, 18095, 1142, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 19237) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 19237), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 19237);
}

// REPEAT 3 - TIME: 7.2393128 s

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

method {:test} Test12() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 1796, 27055, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 28851) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 28851), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 28851);
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 19, 0, 0, 2282, 27018, 0, 0, 0, 21, 0, 0, 0, 16, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 29300) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 29300), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 29300);
}
method {:test} Test14() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 8855, 21792, 9];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 30647) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 30647), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 30647);
}

// REPEAT 5 - TIME: 11.0790247 s

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

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 45432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 47869) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 47869), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 47869);
}
method {:test} Test20() {
var seqint0 : seq<int> := [0, 8855, 31955, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 40810) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 40810), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 40810);
}

// REPEAT 7 - TIME: 15.1207989 s

method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 54288, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 56725) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 56725), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 56725);
}
method {:test} Test23() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 41787, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 50152) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 50152), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 50152);
}

// REPEAT 8 - TIME: 17.1205323 s

method {:test} Test24() {
var seqint0 : seq<int> := [0, 50157, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 58522) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 58522), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 58522);
}
method {:test} Test26() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 63144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 65581) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 65581), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 65581);
}

// REPEAT 9 - TIME: 19.6012751 s

method {:test} Test27() {
var seqint0 : seq<int> := [0, 59013, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 67378) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 67378), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 67378);
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 449, 65742, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 66191) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 66191), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 66191);
}

// REPEAT 10 - TIME: 22.228605 s
