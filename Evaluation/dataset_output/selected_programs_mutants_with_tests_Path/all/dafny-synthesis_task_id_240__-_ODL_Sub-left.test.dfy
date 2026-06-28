// dafny-synthesis_task_id_240.dfy

method {:testEntry} ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
  requires |first| > 0
  ensures |result| == |first| - 1 + |second|
  ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
  ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{
  result := first[0 .. 1] + second;
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 1 - TIME: 2.7063466 s

method {:test} Test1() {
var seqint0 : seq<int> := [3, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 1];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 2 - TIME: 3.6565299 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [2];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 3 - TIME: 4.7754982 s

method {:test} Test3() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
var seqint1 : seq<int> := [0, 0, 0, 0, 4];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 4 - TIME: 5.7833056 s

method {:test} Test4() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 0, 11, 0];
var seqint1 : seq<int> := [0, 5, 0, 0, 0, 13];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 5 - TIME: 6.7220258 s

method {:test} Test5() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [15, 7];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 6 - TIME: 7.617494 s

method {:test} Test6() {
var seqint0 : seq<int> := [22, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0];
var seqint1 : seq<int> := [20, 0, 16];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 7 - TIME: 8.523778 s

method {:test} Test7() {
var seqint0 : seq<int> := [31, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 27, 29];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 14, 23, 25];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 8 - TIME: 9.3774727 s

method {:test} Test8() {
var seqint0 : seq<int> := [34, 0, 17];
var seqint1 : seq<int> := [32, 0, 24, 28];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 9 - TIME: 10.2983183 s

method {:test} Test9() {
var seqint0 : seq<int> := [51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 49, 35, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 21, 0, 39, 0, 30, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 0, 43];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 10 - TIME: 11.2542332 s
