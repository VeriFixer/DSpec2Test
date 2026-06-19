// dafny-synthesis_task_id_728.dfy

method {:testEntry} AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
  result := [1, 2, 3];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
    result := result + [a[i] + b[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 1 - TIME: 2.8270197 s

method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 2 - TIME: 3.7721284 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, -6483];
var seqint1 : seq<int> := [0, 7719];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 3 - TIME: 4.6017893 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 0, 0, 609, 0, 0, 0, 0, 0, 0, 535, 0, 0, 0, 0, 0, 8365];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8098, 0, 0, 0, 449, 0, 0, 0, 0, 0, 0, 5385, 0, 0, 0, 0, 0, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 4 - TIME: 5.8038746 s

method {:test} Test4() {
var seqint0 : seq<int> := [-2662, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7059, -5404];
var seqint1 : seq<int> := [8945, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8855, 5853];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 5 - TIME: 6.7560965 s

method {:test} Test5() {
var seqint0 : seq<int> := [4679, 8855, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7719];
var seqint1 : seq<int> := [974, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 6 - TIME: 7.7275892 s

method {:test} Test6() {
var seqint0 : seq<int> := [1888, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 0, 2437];
var seqint1 : seq<int> := [1653, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2282, 0, 8855];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 8.7043475 s

method {:test} Test7() {
var seqint0 : seq<int> := [8879, 2437, 0, 0, 0, 0, 0, 2282, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [-7556, -1201, 0, 0, 0, 0, 0, 6083, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 8 - TIME: 9.5386287 s

method {:test} Test8() {
var seqint0 : seq<int> := [449, 0, 1236];
var seqint1 : seq<int> := [1833, 0, 6483];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 10.2896968 s

method {:test} Test9() {
var seqint0 : seq<int> := [1108, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
var seqint1 : seq<int> := [1103, 7059, 0, 0, 0, 0, 0, 0, 0, 0, 6483];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 10 - TIME: 11.2931563 s
