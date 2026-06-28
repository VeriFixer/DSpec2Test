// dafny-synthesis_task_id_586.dfy

method {:testEntry} SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0 && n < |l|
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
{
  var firstPart: seq<int> := [];
  var secondPart: seq<int> := l[n..];
  r := secondPart + firstPart;
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 0 >= 0 && 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 0) % |seqint0|];
}

// REPEAT 1 - TIME: 2.8580768 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 1];
expect 1 >= 0 && 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 1) % |seqint0|];
}

// REPEAT 2 - TIME: 3.7707141 s

method {:test} Test2() {
var seqint0 : seq<int> := [2, 0, 0];
expect 2 >= 0 && 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 2);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 2) % |seqint0|];
}

// REPEAT 3 - TIME: 4.6404397 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 3, 5];
expect 3 >= 0 && 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 3) % |seqint0|];
}

// REPEAT 4 - TIME: 5.7192373 s

method {:test} Test4() {
var seqint0 : seq<int> := [4, 0, 0, 0, 0];
expect 4 >= 0 && 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 4);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 4) % |seqint0|];
}

// REPEAT 5 - TIME: 6.7366195 s

method {:test} Test5() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0];
expect 5 >= 0 && 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 5);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 5) % |seqint0|];
}

// REPEAT 6 - TIME: 7.7925772 s

method {:test} Test6() {
var seqint0 : seq<int> := [9, 0, 0, 0, 7, 0, 0];
expect 6 >= 0 && 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 6);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 6) % |seqint0|];
}

// REPEAT 7 - TIME: 8.7352359 s

method {:test} Test7() {
var seqint0 : seq<int> := [11, 0, 0, 0, 8, 0, 0, 13];
expect 7 >= 0 && 7 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 7);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 7) % |seqint0|];
}

// REPEAT 8 - TIME: 9.5844477 s

method {:test} Test8() {
var seqint0 : seq<int> := [14, 10, 0, 0, 0, 0, 0, 16, 18];
expect 8 >= 0 && 8 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 8);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 8) % |seqint0|];
}

// REPEAT 9 - TIME: 10.3457093 s

method {:test} Test9() {
var seqint0 : seq<int> := [20, 0, 0, 12, 0, 0, 0, 0, 0, 17];
expect 9 >= 0 && 9 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 9);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 9) % |seqint0|];
}

// REPEAT 10 - TIME: 11.2410052 s
