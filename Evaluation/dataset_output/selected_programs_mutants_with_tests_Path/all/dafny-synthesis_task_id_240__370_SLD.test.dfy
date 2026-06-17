// dafny-synthesis_task_id_240.dfy

method {:testEntry} ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
  requires |first| > 0
  ensures |result| == |first| - 1 + |second|
  ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
  ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{
  result := first[0..] + second;
}


method {:testEntry} ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
    requires |first| > 0
    ensures |result| == |first| - 1 + |second|
    ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
    ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{
    result := first[0..|first| - 1] + second;
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

// REPEAT 1 - TIME: 2.3946809 s

method {:test} Test1() {
var seqint0 : seq<int> := [1, 0];
var seqint1 : seq<int> := [0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 2 - TIME: 3.3637677 s

method {:test} Test2() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
var seqint1 : seq<int> := [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 3 - TIME: 4.5267785 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10];
var seqint1 : seq<int> := [12, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 4 - TIME: 5.6106441 s

method {:test} Test4() {
var seqint0 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 5 - TIME: 6.6143144 s

method {:test} Test5() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 6 - TIME: 7.6424107 s

method {:test} Test6() {
var seqint0 : seq<int> := [13, 0, 0, 0, 0];
var seqint1 : seq<int> := [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 7 - TIME: 8.5590527 s

method {:test} Test7() {
var seqint0 : seq<int> := [17, 0, 0, 0];
var seqint1 : seq<int> := [23, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 8 - TIME: 9.4563555 s

method {:test} Test8() {
var seqint0 : seq<int> := [31, 0, 0, 0, 0, 29, 0, 0];
var seqint1 : seq<int> := [33, 0, 0, 0, 27, 0, 0, 22, 0, 0, 0, 0, 0, 0, 25];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 9 - TIME: 10.6083702 s

method {:test} Test9() {
var seqint0 : seq<int> := [45, 0, 0, 0, 0, 0, 0, 28, 37, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [43, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 41, 0, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 10 - TIME: 11.6880334 s
