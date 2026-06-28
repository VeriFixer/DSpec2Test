// dafny-synthesis_task_id_273.dfy

method {:testEntry} SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{
  result := [];
  var i := 0;
  while i <= |a|
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

// REPEAT 1 - TIME: 9.6357545 s

method {:test} Test1() {
var seqint0 : seq<int> := [10651];
var seqint1 : seq<int> := [8855];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 2 - TIME: 15.9555565 s

method {:test} Test2() {
var seqint0 : seq<int> := [8098];
var seqint1 : seq<int> := [609];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 3 - TIME: 24.3862382 s

method {:test} Test3() {
var seqint0 : seq<int> := [535, 0];
var seqint1 : seq<int> := [254, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 4 - TIME: 33.0904565 s

method {:test} Test4() {
var seqint0 : seq<int> := [449, 0];
var seqint1 : seq<int> := [-1833, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 5 - TIME: 42.8005503 s

method {:test} Test5() {
var seqint0 : seq<int> := [8365, 0, 5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2997];
var seqint1 : seq<int> := [6569, 0, 5385, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3286];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 6 - TIME: 50.1005245 s

method {:test} Test6() {
var seqint0 : seq<int> := [5904];
var seqint1 : seq<int> := [4251];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 7 - TIME: 58.426673 s

method {:test} Test7() {
var seqint0 : seq<int> := [8098, 0, 0];
var seqint1 : seq<int> := [2245, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 8 - TIME: 65.4564068 s

method {:test} Test8() {
var seqint0 : seq<int> := [7065, 0, 2616, 0, 0, 0, 0, 6906, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9725, 0];
var seqint1 : seq<int> := [-513, 0, 170, 0, 0, 0, 0, -1680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7485, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 9 - TIME: 74.5385562 s

method {:test} Test9() {
var seqint0 : seq<int> := [8098, 0, 0, 1236];
var seqint1 : seq<int> := [2245, 0, 0, -7619];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 10 - TIME: 83.1928411 s
