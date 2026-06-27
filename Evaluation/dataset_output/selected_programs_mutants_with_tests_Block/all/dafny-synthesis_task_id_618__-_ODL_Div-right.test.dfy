// dafny-synthesis_task_id_618.dfy

method {:testEntry} ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |b| ==> b[i] != 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] / b[k]
  {
    result := result + [a[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [2437];
var seqint1 : seq<int> := [-1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 1 - TIME: 2.3288775 s

method {:test} Test1() {
var seqint0 : seq<int> := [4339, 3];
var seqint1 : seq<int> := [-8099, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 2 - TIME: 3.156067 s

method {:test} Test2() {
var seqint0 : seq<int> := [535];
var seqint1 : seq<int> := [-536];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 3 - TIME: 3.9312085 s

method {:test} Test3() {
var seqint0 : seq<int> := [-15307825, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [-6284, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 4 - TIME: 4.7406658 s

method {:test} Test4() {
var seqint0 : seq<int> := [-21792457, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [-8946, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 5 - TIME: 5.6018491 s

method {:test} Test5() {
var seqint0 : seq<int> := [-686953, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0];
var seqint1 : seq<int> := [-282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 93, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 6 - TIME: 6.6027944 s

method {:test} Test6() {
var seqint0 : seq<int> := [-2437, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11];
var seqint1 : seq<int> := [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 113, 0, 115];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 7 - TIME: 7.3552882 s

method {:test} Test7() {
var seqint0 : seq<int> := [1142, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [-1143, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 8 - TIME: 8.1626683 s

method {:test} Test8() {
var seqint0 : seq<int> := [1142, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [-1143, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 9 - TIME: 9.0999881 s

method {:test} Test9() {
var seqint0 : seq<int> := [1142, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 13, 15, 17];
var seqint1 : seq<int> := [-1143, 0, 0, 0, 0, 160, 0, 0, 0, 0, 0, 0, 164, 0, 163];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 10 - TIME: 9.7992625 s
