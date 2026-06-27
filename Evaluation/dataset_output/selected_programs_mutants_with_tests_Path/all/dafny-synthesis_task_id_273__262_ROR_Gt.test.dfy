// dafny-synthesis_task_id_273.dfy

method {:testEntry} SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{
  result := [];
  var i := 0;
  while i > |a|
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

// REPEAT 1 - TIME: 10.7395121 s

method {:test} Test1() {
var seqint0 : seq<int> := [1796];
var seqint1 : seq<int> := [-7059];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 2 - TIME: 18.5548711 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 3 - TIME: 25.959115 s

method {:test} Test3() {
var seqint0 : seq<int> := [8955, 0, 8855];
var seqint1 : seq<int> := [1236, 0, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 4 - TIME: 34.1156951 s

method {:test} Test4() {
var seqint0 : seq<int> := [1236, 0, 0, 0];
var seqint1 : seq<int> := [-6483, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 5 - TIME: 41.6318546 s

method {:test} Test5() {
var seqint0 : seq<int> := [6283, 0, 1796];
var seqint1 : seq<int> := [-2662, 0, -7059];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 6 - TIME: 51.8240055 s

method {:test} Test6() {
var seqint0 : seq<int> := [8098, 0, 0, 0, 0];
var seqint1 : seq<int> := [2245, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 7 - TIME: 60.7517887 s

method {:test} Test7() {
var seqint0 : seq<int> := [2455, 6283, 8098];
var seqint1 : seq<int> := [-161, -2662, 2245];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 8 - TIME: 72.3602256 s

method {:test} Test8() {
var seqint0 : seq<int> := [974, 0, 6283, 0, 0, 0];
var seqint1 : seq<int> := [-3705, 0, -2662, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 9 - TIME: 81.6961097 s

method {:test} Test9() {
var seqint0 : seq<int> := [1323, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [-2661, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 10 - TIME: 89.9364303 s
