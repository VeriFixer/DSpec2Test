// dafny-synthesis_task_id_728.dfy

method {:testEntry} AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
  result := [];
  for i := -1 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
  {
    result := result + [a[i] + b[i]];
  }
}


method {:testEntry} AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
    result := [];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == a[k] + b[k]
    {
        result := result + [a[i] + b[i]];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 1 - TIME: 9.9963183 s

method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 2 - TIME: 16.7308946 s

method {:test} Test2() {
var seqint0 : seq<int> := [7059];
var seqint1 : seq<int> := [1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 3 - TIME: 23.8605322 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 4 - TIME: 31.0001684 s

method {:test} Test4() {
var seqint0 : seq<int> := [-7059, 0, 7719];
var seqint1 : seq<int> := [8855, 0, 1236];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 5 - TIME: 38.0896609 s

method {:test} Test5() {
var seqint0 : seq<int> := [-7058, 0, 0];
var seqint1 : seq<int> := [5853, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 6 - TIME: 45.4639048 s

method {:test} Test6() {
var seqint0 : seq<int> := [5385, 0, -6956, 0, 0, 0, 0, 0, 0, 0, 0, -3286];
var seqint1 : seq<int> := [535, 0, 8098, 0, 0, 0, 0, 0, 0, 0, 0, 6283];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 50.7602855 s

method {:test} Test7() {
var seqint0 : seq<int> := [5244, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1682, 0, 3025, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -861];
var seqint1 : seq<int> := [609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2997, 0, 5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 8 - TIME: 58.8090242 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 254, 2245];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 281, 5853];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 66.5054449 s

method {:test} Test9() {
var seqint0 : seq<int> := [-861, 0, 3025, 0, 0, 0, 0, 0, -7133, 0, 0, 1682, 7485];
var seqint1 : seq<int> := [1142, 0, 5920, 0, 0, 0, 0, 0, 8456, 0, 0, 2997, 2240];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 10 - TIME: 76.1305236 s
