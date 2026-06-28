// dafny-synthesis_task_id_273.dfy

method {:testEntry} SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{
  result := [];
  var i := 0;
  while i == |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] - b[k]
  {
    result := result + [a[i] - b[i]];
    i := i + 1;
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 1 - TIME: 3.1782442 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 10651];
var seqint1 : seq<int> := [0, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 2 - TIME: 4.0485531 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 3 - TIME: 4.939692 s

method {:test} Test3() {
var seqint0 : seq<int> := [6201, 1236, 0];
var seqint1 : seq<int> := [281, -1201, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 4 - TIME: 5.8602505 s

method {:test} Test4() {
var seqint0 : seq<int> := [8945, 0];
var seqint1 : seq<int> := [2662, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 5 - TIME: 6.8293967 s

method {:test} Test5() {
var seqint0 : seq<int> := [1653, 0, 0, 0, 0, 0, 8855, 0, 0, 0, 0, 0, 0, 281, 0];
var seqint1 : seq<int> := [-235, 0, 0, 0, 0, 0, 6418, 0, 0, 0, 0, 0, 0, -861, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 6 - TIME: 7.756026 s

method {:test} Test6() {
var seqint0 : seq<int> := [816, 10651, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8955, 0, 0];
var seqint1 : seq<int> := [535, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 7 - TIME: 8.9696676 s

method {:test} Test7() {
var seqint0 : seq<int> := [10202, 0, 0, 2731, 816, 13951];
var seqint1 : seq<int> := [8879, 0, 0, 449, 535, 8098];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 8 - TIME: 10.0643711 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 2282, 0, 0, 0, 0, 8945, 0, 4679, 0, 8855, 0, 0];
var seqint1 : seq<int> := [0, 449, 0, 0, 0, 0, 6283, 0, 974, 0, 1796, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 9 - TIME: 11.0376526 s

method {:test} Test9() {
var seqint0 : seq<int> := [1235, 1796, 0, 0];
var seqint1 : seq<int> := [3609, 2437, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 10 - TIME: 11.9315533 s
