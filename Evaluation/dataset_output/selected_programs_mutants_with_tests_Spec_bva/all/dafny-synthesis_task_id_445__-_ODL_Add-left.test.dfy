// dafny-synthesis_task_id_445.dfy

method {:testEntry} MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] * b[k]
  {
    result := [a[i] * b[i]];
    i := 1;
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
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 1 - TIME: 10.9585041 s

method {:test} Test13() {
var seqint0 : seq<int> := [5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2240];
var seqint1 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 2 - TIME: 11.805488 s

method {:test} Test14() {
var seqint0 : seq<int> := [1, 0, 0];
var seqint1 : seq<int> := [5920, 0, 5853];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 3 - TIME: 12.7372652 s

method {:test} Test15() {
var seqint0 : seq<int> := [5921, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8855];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 4 - TIME: 13.6208394 s

method {:test} Test16() {
var seqint0 : seq<int> := [2240, 0, 0, 5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 435, 0, 0, 6812];
var seqint1 : seq<int> := [1, 0, 5853, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 5 - TIME: 14.5150783 s

method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 8855, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [2240, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 4386];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 6 - TIME: 15.659828 s

method {:test} Test18() {
var seqint0 : seq<int> := [1, 1391];
var seqint1 : seq<int> := [2, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 7 - TIME: 17.0585347 s

method {:test} Test19() {
var seqint0 : seq<int> := [2240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [7856, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 8855];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 8 - TIME: 18.2353912 s

method {:test} Test20() {
var seqint0 : seq<int> := [2, 0, 1818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [2, 8940, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 9 - TIME: 19.2904883 s

method {:test} Test21() {
var seqint0 : seq<int> := [2147, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5854];
var seqint1 : seq<int> := [0, 0, 0, 0, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MultiplyElements(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] * seqint1[i];
}

// REPEAT 10 - TIME: 20.414099 s
