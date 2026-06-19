// dafny-synthesis_task_id_623.dfy

method {:testEntry} PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
  requires n >= 0
  ensures |result| == |l|
  ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{
  result := [];
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == Power(l[k], n)
  {
    result := result;
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
var seqint0 : seq<int> := [25];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 0);
}

// REPEAT 1 - TIME: 2.4936369 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
expect 5854 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5854);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5854);
}

// REPEAT 2 - TIME: 3.3954666 s

method {:test} Test2() {
var seqint0 : seq<int> := [1236, 0];
expect 5855 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5855);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5855);
}

// REPEAT 3 - TIME: 4.3324316 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5];
expect 5856 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5856);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5856);
}

// REPEAT 4 - TIME: 5.181108 s

method {:test} Test4() {
var seqint0 : seq<int> := [1236, 0, 0];
expect 5857 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5857);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5857);
}

// REPEAT 5 - TIME: 6.0357202 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 7, 0, 4];
expect 5858 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5858);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5858);
}

// REPEAT 6 - TIME: 6.963023 s

method {:test} Test6() {
var seqint0 : seq<int> := [1236];
expect 5859 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5859);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5859);
}

// REPEAT 7 - TIME: 7.8076645 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 9, 6];
expect 5860 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5860);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5860);
}

// REPEAT 8 - TIME: 8.4519111 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 13, 0, 8, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 15];
expect 5861 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5861);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5861);
}

// REPEAT 9 - TIME: 9.3284569 s

method {:test} Test9() {
var seqint0 : seq<int> := [2282, 17, 10, 0, 0, 0, 21, 0, 19, 0, 0, 0, 0, 14, 23];
expect 5862 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 5862);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 5862);
}

// REPEAT 10 - TIME: 10.0053059 s
