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
var seqint0 : seq<int> := [8855];
var seqint1 : seq<int> := [1236];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 1 - TIME: 2.3785149 s

method {:test} Test1() {
var seqint0 : seq<int> := [10161, 0];
var seqint1 : seq<int> := [8365, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 2 - TIME: 3.212795 s

method {:test} Test2() {
var seqint0 : seq<int> := [449];
var seqint1 : seq<int> := [-160];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 3 - TIME: 4.1351572 s

method {:test} Test3() {
var seqint0 : seq<int> := [6462, 0, 0];
var seqint1 : seq<int> := [5853, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 4 - TIME: 5.1202313 s

method {:test} Test4() {
var seqint0 : seq<int> := [6455, 8879, 0];
var seqint1 : seq<int> := [5920, 2240, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 5 - TIME: 6.1957397 s

method {:test} Test5() {
var seqint0 : seq<int> := [2282, 535, 974, 8879];
var seqint1 : seq<int> := [1833, 5920, 1888, 2240];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 6 - TIME: 7.0370543 s

method {:test} Test6() {
var seqint0 : seq<int> := [6002, 0, 0, 8586, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [4679, 0, 0, 6906, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 7 - TIME: 7.9003745 s

method {:test} Test7() {
var seqint0 : seq<int> := [7719, 0, 0, 8879, 6878];
var seqint1 : seq<int> := [7110, 8, 0, 2240, 8221];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 8 - TIME: 8.6638455 s

method {:test} Test8() {
var seqint0 : seq<int> := [449, 0];
var seqint1 : seq<int> := [-160, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 9 - TIME: 9.3536087 s

method {:test} Test9() {
var seqint0 : seq<int> := [7719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
var seqint1 : seq<int> := [5282, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SubtractSequences(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] - seqint1[i];
}

// REPEAT 10 - TIME: 9.978264 s
