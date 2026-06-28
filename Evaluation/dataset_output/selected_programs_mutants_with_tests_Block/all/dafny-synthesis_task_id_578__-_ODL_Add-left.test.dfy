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
var seqint0 : seq<int> := [4];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [2];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 1 - TIME: 2.4642943 s

method {:test} Test1() {
var seqint0 : seq<int> := [1];
var seqint1 : seq<int> := [5];
var seqint2 : seq<int> := [7];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 2 - TIME: 3.5222985 s

method {:test} Test2() {
var seqint0 : seq<int> := [10, 0];
var seqint1 : seq<int> := [8, 0];
var seqint2 : seq<int> := [3, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 3 - TIME: 4.5945716 s

method {:test} Test3() {
var seqint0 : seq<int> := [13, 0, 0];
var seqint1 : seq<int> := [6, 0, 0];
var seqint2 : seq<int> := [11, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 4 - TIME: 5.3361872 s

method {:test} Test4() {
var seqint0 : seq<int> := [16, 0, 0, 0];
var seqint1 : seq<int> := [14, 0, 0, 0];
var seqint2 : seq<int> := [9, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 5 - TIME: 6.1881052 s

method {:test} Test5() {
var seqint0 : seq<int> := [19, 0, 0, 0, 0];
var seqint1 : seq<int> := [12, 0, 0, 0, 0];
var seqint2 : seq<int> := [17, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 6 - TIME: 7.0519515 s

method {:test} Test6() {
var seqint0 : seq<int> := [15, 0, 0];
var seqint1 : seq<int> := [20, 0, 0];
var seqint2 : seq<int> := [22, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 7 - TIME: 7.759133 s

method {:test} Test7() {
var seqint0 : seq<int> := [25, 0, 0, 29, 0, 0];
var seqint1 : seq<int> := [18, 0, 0, 0, 31, 0];
var seqint2 : seq<int> := [23, 0, 0, 0, 0, 27];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 8 - TIME: 8.5519966 s

method {:test} Test8() {
var seqint0 : seq<int> := [21, 0, 0, 0, 37, 0, 43];
var seqint1 : seq<int> := [30, 0, 0, 0, 0, 41, 0];
var seqint2 : seq<int> := [26, 0, 0, 0, 33, 39, 35];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 9 - TIME: 9.3776299 s

method {:test} Test9() {
var seqint0 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [32, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [36, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 10 - TIME: 10.244664 s
