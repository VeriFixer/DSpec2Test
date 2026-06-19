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

// REPEAT 1 - TIME: 3.0673162 s

method {:test} Test1() {
var seqint0 : seq<int> := [0];
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1);
}

// REPEAT 2 - TIME: 4.2711069 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2);
}

// REPEAT 3 - TIME: 5.2209169 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 8855, 0, 0, 0, 0];
expect 7068 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7068);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7068);
}

// REPEAT 4 - TIME: 6.010794 s

method {:test} Test4() {
var seqint0 : seq<int> := [1, 0];
expect 7069 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7069);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7069);
}

// REPEAT 5 - TIME: 6.925643 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0];
expect 7070 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7070);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7070);
}

// REPEAT 6 - TIME: 7.752422 s

method {:test} Test6() {
var seqint0 : seq<int> := [2, 9270];
expect 7071 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7071);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7071);
}

// REPEAT 7 - TIME: 8.5017239 s

method {:test} Test7() {
var seqint0 : seq<int> := [3, 0, 0, 0, 211];
expect 7072 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7072);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7072);
}

// REPEAT 8 - TIME: 9.2499809 s

method {:test} Test8() {
var seqint0 : seq<int> := [2446, 0, 0];
expect 7073 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7073);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7073);
}

// REPEAT 9 - TIME: 9.994739 s

method {:test} Test9() {
var seqint0 : seq<int> := [2447, 0, 1236, 609];
expect 7074 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7074);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7074);
}

// REPEAT 10 - TIME: 10.7437817 s
