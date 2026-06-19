// dafny-synthesis_task_id_743.dfy

method {:testEntry} RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
  var rotated: seq<int> := [];
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant |rotated| == i
    invariant forall k :: 0 <= k < i ==> rotated[k] == l[(k - n + |l|) % |l|]
  {
    rotated := rotated + [l[|l|]];
  }
  return rotated;
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 0 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.5987337 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0];
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 1 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.5249813 s

method {:test} Test2() {
var seqint0 : seq<int> := [1, 0, 3];
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 2);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 2 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 4.5697827 s

method {:test} Test3() {
var seqint0 : seq<int> := [2, 0, 0];
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 3 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 5.6469135 s

method {:test} Test4() {
var seqint0 : seq<int> := [4];
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 4);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 4 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 6.5936324 s

method {:test} Test5() {
var seqint0 : seq<int> := [];
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 5);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 5 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 7.6365356 s

method {:test} Test6() {
var seqint0 : seq<int> := [5];
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 6);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 6 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 8.6040372 s

method {:test} Test7() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 7);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 7 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 9.6141297 s

method {:test} Test8() {
var seqint0 : seq<int> := [7, 0, 0, 10];
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 8);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 8 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 10.3901433 s

method {:test} Test9() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 12, 0, 0, 16];
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 9);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 9 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 11.0709071 s
