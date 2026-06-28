// dafny-synthesis_task_id_578.dfy

method {:testEntry} Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    returns (r: seq<int>)
  requires |s1| == |s2| && |s2| == |s3|
  ensures |r| == 3 * |s1|
  ensures forall i :: 0 <= i < |s1| ==> r[3 * i] == s1[i] && r[3 * i + 1] == s2[i] && r[3 * i + 2] == s3[i]
{
  r := [];
  for i := 0 to 0
    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant forall k :: 0 <= k < i ==> r[3 * k] == s1[k] && r[3 * k + 1] == s2[k] && r[3 * k + 2] == s3[k]
  {
    r := r + [s1[i], s2[i], s3[i]];
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

// REPEAT 1 - TIME: 18.865064 s

method {:test} Test1() {
var seqint0 : seq<int> := [37, 0];
var seqint1 : seq<int> := [38, 0];
var seqint2 : seq<int> := [36, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 2 - TIME: 37.1468572 s

method {:test} Test2() {
var seqint0 : seq<int> := [49, 0];
var seqint1 : seq<int> := [54, 0];
var seqint2 : seq<int> := [50, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 3 - TIME: 57.2472846 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 46];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 47];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 44];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 4 - TIME: 78.0009605 s

method {:test} Test4() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 5 - TIME: 101.7091105 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 58, 0];
var seqint1 : seq<int> := [0, 0, 0, 59, 0];
var seqint2 : seq<int> := [0, 0, 0, 57, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 6 - TIME: 128.2037749 s

method {:test} Test6() {
var seqint0 : seq<int> := [89, 0, 72, 63];
var seqint1 : seq<int> := [90, 0, 65, 80];
var seqint2 : seq<int> := [94, 0, 66, 64];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 7 - TIME: 162.5236942 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 85, 109, 120, 104, 126, 112];
var seqint1 : seq<int> := [0, 0, 0, 0, 86, 110, 121, 105, 125, 97];
var seqint2 : seq<int> := [0, 0, 0, 0, 84, 108, 119, 103, 124, 111];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 8 - TIME: 209.94191 s

method {:test} Test8() {
var seqint0 : seq<int> := [122, 0, 0];
var seqint1 : seq<int> := [123, 0, 0];
var seqint2 : seq<int> := [127, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 9 - TIME: 259.8509704 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 131, 143];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 132, 144];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 129, 142];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 10 - TIME: 308.6109493 s
