// dafny-synthesis_task_id_623.dfy

method {:testEntry} PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
  requires n >= 0
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
  result := [1, 2, 3];
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
  {
    result := result + [Power(l[i], n)];
  }
}

function Power(base: int, exponent: int): int
  requires exponent >= 0
{
  if exponent == 0 then
    1
  else
    base * Power(base, exponent - 1)
}


method {:test} Test0() {
var seqint0 : seq<int> := [];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 0);
}
method {:test} Test2() {
var seqint0 : seq<int> := [0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [];
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 100);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 100);
}

// REPEAT 1 - TIME: 11.7375056 s

method {:test} Test12() {
var seqint0 : seq<int> := [1, 0];
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 101);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 101);
}

// REPEAT 2 - TIME: 12.8067377 s

method {:test} Test13() {
var seqint0 : seq<int> := [0, 2437, 0, 0, 0, 0, 609];
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 102);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 102);
}

// REPEAT 3 - TIME: 13.8312599 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 2437];
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 103);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 103);
}

// REPEAT 4 - TIME: 14.8756204 s

method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 609];
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 104);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 104);
}

// REPEAT 5 - TIME: 15.8821501 s

method {:test} Test16() {
var seqint0 : seq<int> := [609, 0, 1236, 0, 0, 0, 0, 0, 0];
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 105);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 105);
}

// REPEAT 6 - TIME: 16.83801 s

method {:test} Test17() {
var seqint0 : seq<int> := [5904, 1236, 0, 0];
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 106);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 106);
}

// REPEAT 7 - TIME: 18.1010537 s

method {:test} Test18() {
var seqint0 : seq<int> := [582, 0, 5853, 0, 0];
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 107);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 107);
}

// REPEAT 8 - TIME: 19.1220215 s

method {:test} Test19() {
var seqint0 : seq<int> := [3961, 0, 0];
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 108);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 108);
}

// REPEAT 9 - TIME: 20.127978 s

method {:test} Test20() {
var seqint0 : seq<int> := [3504, 0, 1, 0];
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 109);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 109);
}

// REPEAT 10 - TIME: 21.2817566 s
