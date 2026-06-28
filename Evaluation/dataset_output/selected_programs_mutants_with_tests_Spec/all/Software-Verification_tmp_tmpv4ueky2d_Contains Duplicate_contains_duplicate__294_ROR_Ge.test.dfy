// Software-Verification_tmp_tmpv4ueky2d_Contains Duplicate_contains_duplicate.dfy

method {:testEntry} contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> distinct(nums)
{
  var i := 0;
  var s: set<int> := {};
  while i >= |nums|
    invariant i <= |nums|
    invariant forall j :: j in nums[..i] <==> j in s
    invariant distinct(nums[..i])
  {
    var num := nums[i];
    if num in s {
      return false;
    }
    s := s + {num};
    i := i + 1;
  }
  return true;
}

predicate distinct(nums: seq<int>)
{
  forall i, j :: 
    0 <= i < j < |nums| ==>
      nums[i] != nums[j]
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991145, -999991145];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 1 - TIME: 3.3710613 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999992281];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, -999991145, -999991145];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 2 - TIME: 4.7763007 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, -999991043, -999998764, -999998763];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [-999997718, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991635, -999998204, -999998204, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 3 - TIME: 6.0905392 s

method {:test} Test6() {
var seqint0 : seq<int> := [-999992279, -999992280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999992281, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [-999997717, -999997717];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 4 - TIME: 7.6094221 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, -999998757, -999998759, -999998760, 0, 0, 0, 0, 0, 0, 0, -999998761, 0, 0, 0, 0, -999998758, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, -999991635, -999991635, 0, 0, -999997718, 0, 0, 0, 0, -999999551, 0, 0, 0, 0, 0, 0, -999999391, -999994147, 0, -999991902];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 5 - TIME: 9.4422286 s

method {:test} Test10() {
var seqint0 : seq<int> := [0, 0, 0, 0, -999997559, 0, 0, 0, 0, -999997558, 0, 0, -999997557, 0, 0, 0, 0, -999997560, -999997561, -999997562, -999997563, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, -999991635, -999991635, 0, 0, 0, 0, 0, 0, -999997718, 0, 0, -999999391, -999994147, -999991902, 0, -999999551];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 6 - TIME: 10.9708621 s

method {:test} Test12() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999994141, -999994142, -999994147, 0, 0, 0, 0, -999994144, -999994146, 0, -999994143, 0, -999994145];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, -999991055, 0, 0, -999994147, 0, 0, -999998858, 0, 0, 0, 0, 0, -999999551, -999999551, -999997003, -999995321, -999999026, -999998112, -999994096];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 7 - TIME: 12.0336455 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, -999994141, -999994140, 0, 0, 0, -999994147, 0, 0, -999994142, -999994146, -999994145, 0, -999994144, -999994143, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, -999999391, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999994147, -999991902, -999998858, 0, 0, -999991635, -999991635];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 8 - TIME: 13.3912973 s

method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, -999998197, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998198, 0, -999998199, 0, -999999668, -999999669, -999999666, -999999665, 0, -999999667];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, -999994147, 0, 0, 0, -999999551, 0, -999997718, -999997718, 0, 0, 0, 0, 0, 0, 0, -999991902, 0, -999998858, -999999719, -999997003, -999991055];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 9 - TIME: 14.6736705 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991145, -999991145, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 10 - TIME: 16.1484328 s
