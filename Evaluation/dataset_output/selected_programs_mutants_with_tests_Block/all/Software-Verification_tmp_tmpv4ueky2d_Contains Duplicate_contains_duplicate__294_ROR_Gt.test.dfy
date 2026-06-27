// Software-Verification_tmp_tmpv4ueky2d_Contains Duplicate_contains_duplicate.dfy

method {:testEntry} contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> distinct(nums)
{
  var i := 0;
  var s: set<int> := {};
  while i > |nums|
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
var seqint0 : seq<int> := [0, 0, -999999551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999551];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 1 - TIME: 3.1386448 s

method {:test} Test2() {
var seqint0 : seq<int> := [-999998764, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, -999991635, 0, 0, -999991635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991636, -999998204];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 2 - TIME: 4.8596928 s

method {:test} Test4() {
var seqint0 : seq<int> := [-999991145, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [-999999391, 0, -999994147, 0, -999994147, 0, -999997718];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 3 - TIME: 6.5494222 s

method {:test} Test6() {
var seqint0 : seq<int> := [-999991635, 0, 0, 0, 0, 0, -999991634, -999991633];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [-999994147, 0, 0, -999993717, 0, 0, 0, -999993717, -999999391, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998858, 0, -999994080, -999993718];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 4 - TIME: 8.1080974 s

method {:test} Test8() {
var seqint0 : seq<int> := [-999994079, 0, 0, 0, 0, 0, 0, -999994080, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, -999991635, -999991635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 5 - TIME: 9.8009944 s

method {:test} Test10() {
var seqint0 : seq<int> := [-999999963, 0, 0, 0, 0, 0, -999999962, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [-999997003, 0, 0, 0, 0, -999995321, 0, 0, 0, 0, -999995321, -999999551, -999999391];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 6 - TIME: 11.4847068 s

method {:test} Test12() {
var seqint0 : seq<int> := [-999999719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999992281, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [-999991635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991635, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 7 - TIME: 12.9243411 s

method {:test} Test14() {
var seqint0 : seq<int> := [-999997760, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991902, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999995611, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999995611, -999998857, -999997466, -999997466, 0, -999999390];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 8 - TIME: 14.4644251 s

method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [-999991635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991635, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 9 - TIME: 15.882686 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [-999999551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999999551, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 10 - TIME: 17.3941429 s
