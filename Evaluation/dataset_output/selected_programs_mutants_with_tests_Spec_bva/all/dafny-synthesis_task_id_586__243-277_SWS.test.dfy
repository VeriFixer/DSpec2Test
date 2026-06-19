// dafny-synthesis_task_id_586.dfy

method {:testEntry} SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0 && n < |l|
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
{
  var secondPart: seq<int> := l[n..];
  var firstPart: seq<int> := l[..n];
  r := secondPart + firstPart;
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 0 >= 0 && 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 0) % |seqint0|];
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
expect 0 >= 0 && 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 0) % |seqint0|];
}

// REPEAT 1 - TIME: 7.3248959 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 1, 0];
expect 1 >= 0 && 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 1) % |seqint0|];
}

// REPEAT 2 - TIME: 8.129728 s

method {:test} Test10() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 6];
expect 2 >= 0 && 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 2);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 2) % |seqint0|];
}

// REPEAT 3 - TIME: 8.9542026 s

method {:test} Test11() {
var seqint0 : seq<int> := [3, 0, 0, 0];
expect 3 >= 0 && 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 3) % |seqint0|];
}

// REPEAT 4 - TIME: 9.7526835 s

method {:test} Test12() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 4 >= 0 && 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 4);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 4) % |seqint0|];
}

// REPEAT 5 - TIME: 10.48834 s

method {:test} Test13() {
var seqint0 : seq<int> := [7, 0, 0, 0, 9, 0];
expect 5 >= 0 && 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 5);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 5) % |seqint0|];
}

// REPEAT 6 - TIME: 11.2086922 s

method {:test} Test14() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 11];
expect 6 >= 0 && 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 6);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 6) % |seqint0|];
}

// REPEAT 7 - TIME: 11.979601 s

method {:test} Test15() {
var seqint0 : seq<int> := [17, 0, 0, 0, 10, 13, 15, 0];
expect 7 >= 0 && 7 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 7);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 7) % |seqint0|];
}

// REPEAT 8 - TIME: 12.8915838 s

method {:test} Test16() {
var seqint0 : seq<int> := [19, 0, 12, 0, 0, 0, 0, 16, 0];
expect 8 >= 0 && 8 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 8);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 8) % |seqint0|];
}

// REPEAT 9 - TIME: 13.718894 s

method {:test} Test17() {
var seqint0 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 14, 22, 20];
expect 9 >= 0 && 9 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 9);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 9) % |seqint0|];
}

// REPEAT 10 - TIME: 14.4227022 s
