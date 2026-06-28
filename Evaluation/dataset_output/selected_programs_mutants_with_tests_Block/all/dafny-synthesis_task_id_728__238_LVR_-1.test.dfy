// dafny-synthesis_task_id_728.dfy

method {:testEntry} AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
  result := [];
  for i := -1 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
    result := result + [a[i] + b[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [7719];
var seqint1 : seq<int> := [2437];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 1 - TIME: 2.485978 s

method {:test} Test1() {
var seqint0 : seq<int> := [7719, 0];
var seqint1 : seq<int> := [-5282, 2];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 2 - TIME: 3.2845472 s

method {:test} Test2() {
var seqint0 : seq<int> := [2437, 0, 0];
var seqint1 : seq<int> := [7719, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 3 - TIME: 4.2722802 s

method {:test} Test3() {
var seqint0 : seq<int> := [535, 974];
var seqint1 : seq<int> := [5920, 1888];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 4 - TIME: 5.0921693 s

method {:test} Test4() {
var seqint0 : seq<int> := [7719, 4, 0, 8];
var seqint1 : seq<int> := [-5923, 6, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 5 - TIME: 6.0689323 s

method {:test} Test5() {
var seqint0 : seq<int> := [-5282];
var seqint1 : seq<int> := [7719];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 6 - TIME: 6.8603314 s

method {:test} Test6() {
var seqint0 : seq<int> := [449, 0, 0, 0, 5];
var seqint1 : seq<int> := [160, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 7.5597031 s

method {:test} Test7() {
var seqint0 : seq<int> := [-5385];
var seqint1 : seq<int> := [5920];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 8 - TIME: 8.2693867 s

method {:test} Test8() {
var seqint0 : seq<int> := [7719, 0, 0, 0, 0, 10];
var seqint1 : seq<int> := [646, 0, 0, 7, 12, 14];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 9.031484 s

method {:test} Test9() {
var seqint0 : seq<int> := [7619];
var seqint1 : seq<int> := [1236];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 10 - TIME: 9.6261921 s
