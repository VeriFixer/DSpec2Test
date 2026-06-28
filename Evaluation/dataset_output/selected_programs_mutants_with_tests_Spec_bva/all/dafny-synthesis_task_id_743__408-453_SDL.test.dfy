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
method {:test} Test1() {
var seqint0 : seq<int> := [];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 0 + |seqint0|) % |seqint0|];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 0 + |seqint0|) % |seqint0|];
}
method {:test} Test5() {
var seqint0 : seq<int> := [0];
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 100);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 100 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 10.7099253 s

method {:test} Test12() {
var seqint0 : seq<int> := [1, 0];
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 101);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 101 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 11.7434979 s

method {:test} Test13() {
var seqint0 : seq<int> := [2, 0];
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 102);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 102 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 12.7048046 s

method {:test} Test14() {
var seqint0 : seq<int> := [3, 0, 5];
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 103);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 103 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 13.7172623 s

method {:test} Test15() {
var seqint0 : seq<int> := [4, 7];
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 104);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 104 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 14.6860167 s

method {:test} Test16() {
var seqint0 : seq<int> := [6, 0];
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 105);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 105 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 15.6601177 s

method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 106);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 106 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 16.298742 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0];
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 107);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 107 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 17.1874894 s

method {:test} Test19() {
var seqint0 : seq<int> := [12, 10, 0, 0];
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 108);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 108 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 18.0510581 s

method {:test} Test20() {
var seqint0 : seq<int> := [16, 11, 0, 14];
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 109);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 109 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 18.8508285 s
