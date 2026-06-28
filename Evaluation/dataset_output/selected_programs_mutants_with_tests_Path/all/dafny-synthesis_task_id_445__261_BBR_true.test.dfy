// dafny-synthesis_task_id_445.dfy

method {:testEntry} MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{
  result := [];
  var i := 0;
  while true
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] * b[k]
  {
    result := result + [a[i] * b[i]];
    i := i + 1;
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 1 - TIME: 12.7222455 s

method {:test} Test1() {
var seqint0 : seq<int> := [2437];
var seqint1 : seq<int> := [1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 2 - TIME: 22.2752015 s

method {:test} Test2() {
var seqint0 : seq<int> := [1, 0];
var seqint1 : seq<int> := [2437, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 3 - TIME: 32.8694311 s

method {:test} Test3() {
var seqint0 : seq<int> := [1, 0, 0];
var seqint1 : seq<int> := [8098, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 4 - TIME: 42.5700998 s

method {:test} Test4() {
var seqint0 : seq<int> := [2211, 0, 7578, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 5 - TIME: 52.1025489 s

method {:test} Test5() {
var seqint0 : seq<int> := [2];
var seqint1 : seq<int> := [2];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 6 - TIME: 63.7959276 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [4679, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 7 - TIME: 77.6585092 s

method {:test} Test7() {
var seqint0 : seq<int> := [1, 0, 0, 0];
var seqint1 : seq<int> := [2437, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 8 - TIME: 90.8006122 s

method {:test} Test8() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0];
var seqint1 : seq<int> := [5853, 0, 9725, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 9 - TIME: 105.8330272 s

method {:test} Test9() {
var seqint0 : seq<int> := [3, 0, 0, 6308, 1];
var seqint1 : seq<int> := [3, 0, 0, 0, 5076];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 10 - TIME: 123.5497084 s
