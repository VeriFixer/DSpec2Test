// dafny-synthesis_task_id_445.dfy

method {:testEntry} MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{
  result := [];
  var i := 0;
  while i == |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] * b[k]
  {
    result := result + [a[i] * b[i]];
    i := i + 1;
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 1 - TIME: 3.1221056 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 1236];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 2 - TIME: 4.1770169 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 449, 0, 0, 0, 0, 1796];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 6283, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 3 - TIME: 4.9932149 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 4 - TIME: 5.9491317 s

method {:test} Test4() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5904];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 5 - TIME: 6.9467642 s

method {:test} Test5() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 6 - TIME: 7.809389 s

method {:test} Test6() {
var seqint0 : seq<int> := [4263, 0, 0, 0, 0, 449];
var seqint1 : seq<int> := [5904, 0, 0, 0, 0, 1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 7 - TIME: 8.8237166 s

method {:test} Test7() {
var seqint0 : seq<int> := [2, 1];
var seqint1 : seq<int> := [9098, 1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 8 - TIME: 9.7838742 s

method {:test} Test8() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0, 0, 1174, 0, 0, 0, 0, 0, 8113, 0, 0, 0];
var seqint1 : seq<int> := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 9588];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 9 - TIME: 10.6638567 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 5904, 1, 0, 0];
var seqint1 : seq<int> := [9531, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6283, 0, 1142];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 10 - TIME: 11.4267486 s
