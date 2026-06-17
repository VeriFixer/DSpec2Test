// dafny-synthesis_task_id_728.dfy

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
    result := result;
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
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 1 - TIME: 7.8268161 s

method {:test} Test13() {
var seqint0 : seq<int> := [7059, 0];
var seqint1 : seq<int> := [1796, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 2 - TIME: 8.555663 s

method {:test} Test14() {
var seqint0 : seq<int> := [-1201, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6569];
var seqint1 : seq<int> := [2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 3 - TIME: 9.2642188 s

method {:test} Test15() {
var seqint0 : seq<int> := [8098, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 449];
var seqint1 : seq<int> := [-2245, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059, 1833];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 4 - TIME: 9.9883936 s

method {:test} Test16() {
var seqint0 : seq<int> := [6283, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
var seqint1 : seq<int> := [-3286, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1201];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 5 - TIME: 10.6664254 s

method {:test} Test17() {
var seqint0 : seq<int> := [9725, 0, 2282, 8855, 5853];
var seqint1 : seq<int> := [-7485, 0, 6083, -6418, -5244];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 6 - TIME: 11.8192893 s

method {:test} Test18() {
var seqint0 : seq<int> := [6283, 0, 0, 0, 0, 1796, 0, 1236, 449];
var seqint1 : seq<int> := [-3285, 0, 0, 0, 0, 6569, 0, 1201, 160];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 12.647208 s

method {:test} Test19() {
var seqint0 : seq<int> := [2275, 0, 0, 449, 0, 2437];
var seqint1 : seq<int> := [171, 0, 0, 160, 0, 6418];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 8 - TIME: 13.437676 s

method {:test} Test20() {
var seqint0 : seq<int> := [2275, 0, 0, 0, 0, 974, 535, 609, 1796, 6283];
var seqint1 : seq<int> := [2446, 0, 0, 0, 0, 1888, 5920, 5853, 8365, 2997];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 14.3236028 s

method {:test} Test21() {
var seqint0 : seq<int> := [8945, 0, 0, 0, 0, 7719, 0, 0, 0, 0, 0, 0, 8855];
var seqint1 : seq<int> := [6283, 0, 0, 0, 0, 1236, 0, 0, 0, 0, 0, 0, 449];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 10 - TIME: 15.1091509 s
