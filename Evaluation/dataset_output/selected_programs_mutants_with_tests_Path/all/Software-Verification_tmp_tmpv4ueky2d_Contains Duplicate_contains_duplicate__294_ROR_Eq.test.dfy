// Software-Verification_tmp_tmpv4ueky2d_Contains Duplicate_contains_duplicate.dfy

method {:testEntry} contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> distinct(nums)
{
  var i := 0;
  var s: set<int> := {};
  while i == |nums|
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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999551];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 1 - TIME: 7.4989859 s

method {:test} Test2() {
var seqint0 : seq<int> := [-999998764, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998763];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, -999998204, -999998204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998205, 0, 0, 0, 0, 0, 0, -999999386];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 2 - TIME: 11.8967449 s

method {:test} Test4() {
var seqint0 : seq<int> := [-999998764, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999996326, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999994147, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999994147, -999999551];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 3 - TIME: 16.33002 s

method {:test} Test6() {
var seqint0 : seq<int> := [-999999551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999550];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, -999999391, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999391, -999999392, 0, -999999925, 0, -999999551];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 4 - TIME: 20.9063285 s

method {:test} Test8() {
var seqint0 : seq<int> := [-999991055, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991054];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [-999999391, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999391, -999999673, 0, 0, -999999551, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 5 - TIME: 26.0895655 s

method {:test} Test10() {
var seqint0 : seq<int> := [-999994096, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999994095];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [-999998859, -999998858, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998858, -999999551];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 6 - TIME: 30.8476107 s

method {:test} Test12() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991635, 0, -999991635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 7 - TIME: 36.1075476 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999997718, -999997718, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 8 - TIME: 41.1639424 s

method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, -999999551, 0, 0, 0, 0, 0, -999999551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 9 - TIME: 47.8166285 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -999997718, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999997718, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 10 - TIME: 54.7430886 s
