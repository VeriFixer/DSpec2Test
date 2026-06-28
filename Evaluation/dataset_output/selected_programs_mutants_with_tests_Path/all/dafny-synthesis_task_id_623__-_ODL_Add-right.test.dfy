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
var seqint0 : seq<int> := [0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 0);
}

// REPEAT 1 - TIME: 14.2404578 s

method {:test} Test1() {
var seqint0 : seq<int> := [2276];
expect 2448 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2448);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2448);
}

// REPEAT 2 - TIME: 24.9012355 s

method {:test} Test2() {
var seqint0 : seq<int> := [1];
expect 2449 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2449);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2449);
}

// REPEAT 3 - TIME: 35.9067993 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
expect 2450 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2450);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2450);
}

// REPEAT 4 - TIME: 48.2247689 s

method {:test} Test4() {
var seqint0 : seq<int> := [3213];
expect 2451 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2451);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2451);
}

// REPEAT 5 - TIME: 62.9611551 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 38];
expect 2452 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2452);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2452);
}

// REPEAT 6 - TIME: 79.508474 s

method {:test} Test6() {
var seqint0 : seq<int> := [1769, 0, 0, 0, 0, 0, 0, 0, 3504];
expect 2453 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2453);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2453);
}

// REPEAT 7 - TIME: 95.9437835 s

method {:test} Test7() {
var seqint0 : seq<int> := [4135, 0, 6878];
expect 2454 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2454);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2454);
}

// REPEAT 8 - TIME: 113.0710982 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0];
expect 2455 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2455);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2455);
}

// REPEAT 9 - TIME: 130.3187859 s

method {:test} Test9() {
var seqint0 : seq<int> := [2655, 0, 5045];
expect 2456 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 2456);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 2456);
}

// REPEAT 10 - TIME: 152.0027595 s
