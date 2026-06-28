// dafny-synthesis_task_id_618.dfy

method {:testEntry} ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |b| ==> b[i] != 0
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] / b[k]
  {
    result := result + [b[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 1 - TIME: 3.0681421 s

method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 2 - TIME: 4.1952843 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 3 - TIME: 5.1685062 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 281, 0, 0, 0, 0, -2437];
var seqint1 : seq<int> := [0, 0, -1, 0, 0, 0, 0, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 4 - TIME: 6.1978478 s

method {:test} Test4() {
var seqint0 : seq<int> := [6890, 1062, 2240, -209161, 0, 0, 0, 0, 3609];
var seqint1 : seq<int> := [-6891, -1063, -1, -747, 0, 0, 0, 0, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 5 - TIME: 7.2400864 s

method {:test} Test5() {
var seqint0 : seq<int> := [8945, 0, 0, 0, 0, 0, 2282];
var seqint1 : seq<int> := [-1, 0, 0, 0, 0, 0, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 6 - TIME: 8.4134124 s

method {:test} Test6() {
var seqint0 : seq<int> := [6758, 0, 0, 0, 0, 0, 0, 1768];
var seqint1 : seq<int> := [-6759, 0, 0, 0, 0, 0, 0, -1769];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 7 - TIME: 9.3834864 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 4335, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, -4336, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 8 - TIME: 10.3820182 s

method {:test} Test8() {
var seqint0 : seq<int> := [5968, 0, 1323];
var seqint1 : seq<int> := [-5969, 0, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 9 - TIME: 11.4093852 s

method {:test} Test9() {
var seqint0 : seq<int> := [690, 0, 0, 0, 0, 0, 0, 609, 5598];
var seqint1 : seq<int> := [-3197, 0, 0, 0, 0, 0, 0, -1, -1];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint1| ==> seqint1[i] != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementWiseDivide(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] / seqint1[i];
}

// REPEAT 10 - TIME: 12.3280089 s
