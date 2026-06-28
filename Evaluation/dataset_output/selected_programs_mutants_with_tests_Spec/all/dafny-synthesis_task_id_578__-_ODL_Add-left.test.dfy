// dafny-synthesis_task_id_578.dfy

method {:testEntry} Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    returns (r: seq<int>)
  requires |s1| == |s2| && |s2| == |s3|
  ensures |r| == 3 * |s1|
  ensures forall i :: 0 <= i < |s1| ==> r[3 * i] == s1[i] && r[3 * i + 1] == s2[i] && r[3 * i + 2] == s3[i]
{
  r := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant forall k :: 0 <= k < i ==> r[3 * k] == s1[k] && r[3 * k + 1] == s2[k] && r[3 * k + 2] == s3[k]
  {
    r := [s1[i], s2[i], s3[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 1 - TIME: 2.9255437 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 34, 0, 39];
var seqint1 : seq<int> := [0, 0, 32, 0, 40];
var seqint2 : seq<int> := [0, 0, 33, 0, 38];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 2 - TIME: 4.2262152 s

method {:test} Test2() {
var seqint0 : seq<int> := [64, 0, 60, 0, 47];
var seqint1 : seq<int> := [69, 0, 51, 0, 48];
var seqint2 : seq<int> := [70, 0, 50, 0, 46];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 3 - TIME: 5.3048869 s

method {:test} Test3() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 4 - TIME: 6.4569914 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 83, 0, 0, 89, 0, 68];
var seqint1 : seq<int> := [0, 0, 0, 0, 78, 0, 0, 88, 0, 72];
var seqint2 : seq<int> := [0, 0, 0, 0, 77, 0, 0, 87, 0, 71];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 5 - TIME: 7.7672631 s

method {:test} Test5() {
var seqint0 : seq<int> := [114, 0, 0, 103, 0, 108];
var seqint1 : seq<int> := [115, 0, 0, 94, 0, 109];
var seqint2 : seq<int> := [113, 0, 0, 92, 0, 107];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 6 - TIME: 8.8620373 s

method {:test} Test6() {
var seqint0 : seq<int> := [112, 0, 0];
var seqint1 : seq<int> := [116, 0, 0];
var seqint2 : seq<int> := [117, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 7 - TIME: 9.5251635 s

method {:test} Test7() {
var seqint0 : seq<int> := [197, 140, 150, 166, 158, 172, 130];
var seqint1 : seq<int> := [195, 138, 152, 167, 156, 188, 128];
var seqint2 : seq<int> := [196, 139, 151, 165, 157, 171, 129];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 8 - TIME: 10.399502 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 169, 0, 0, 181];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 170, 0, 0, 182];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 159, 0, 0, 180];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 9 - TIME: 11.1886912 s

method {:test} Test9() {
var seqint0 : seq<int> := [242, 0, 0, 183, 0, 0, 209, 215, 223, 229];
var seqint1 : seq<int> := [243, 0, 0, 184, 0, 0, 210, 214, 191, 230];
var seqint2 : seq<int> := [244, 0, 0, 185, 0, 0, 211, 216, 224, 231];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 10 - TIME: 12.0520099 s
