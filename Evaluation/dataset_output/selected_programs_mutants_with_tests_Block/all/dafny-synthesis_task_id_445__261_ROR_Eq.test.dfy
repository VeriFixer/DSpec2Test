// dafny-synthesis_task_id_445.dfy

method {:testEntry} MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{
  result := [];
  var i := 0;
  while i == |a|
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
var seqint1 : seq<int> := [1236];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 1 - TIME: 2.3582153 s

method {:test} Test1() {
var seqint0 : seq<int> := [1236, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 2 - TIME: 3.3273882 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [1236, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 3 - TIME: 4.1158158 s

method {:test} Test3() {
var seqint0 : seq<int> := [2437, 0, 7, 5];
var seqint1 : seq<int> := [0, 9, 0, 3];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 4 - TIME: 4.9663125 s

method {:test} Test4() {
var seqint0 : seq<int> := [1236, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 5 - TIME: 5.8631035 s

method {:test} Test5() {
var seqint0 : seq<int> := [2438, 10];
var seqint1 : seq<int> := [1, 6];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 6 - TIME: 6.5795052 s

method {:test} Test6() {
var seqint0 : seq<int> := [1236, 0, 0, 8, 0, 0];
var seqint1 : seq<int> := [536, 0, 0, 0, 12, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 7 - TIME: 7.3956281 s

method {:test} Test7() {
var seqint0 : seq<int> := [1];
var seqint1 : seq<int> := [1237];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 8 - TIME: 8.2137958 s

method {:test} Test8() {
var seqint0 : seq<int> := [2282, 0, 0, 14, 0, 0, 18];
var seqint1 : seq<int> := [1, 0, 11, 0, 0, 0, 16];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 9 - TIME: 8.995418 s

method {:test} Test9() {
var seqint0 : seq<int> := [-2437];
var seqint1 : seq<int> := [-1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 10 - TIME: 9.6987858 s
