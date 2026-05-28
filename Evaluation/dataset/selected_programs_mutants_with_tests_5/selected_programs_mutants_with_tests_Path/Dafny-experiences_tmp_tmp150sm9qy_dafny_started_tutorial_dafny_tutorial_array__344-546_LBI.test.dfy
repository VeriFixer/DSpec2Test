// Dafny-experiences_tmp_tmp150sm9qy_dafny_started_tutorial_dafny_tutorial_array.dfy

method {:testEntry} FindMax(a: seq<int>) returns (i: int)
  requires |a| > 0
  ensures 0 <= i < |a|
  ensures forall k :: 0 <= k < |a| ==> a[k] <= a[i]
{
  i := 0;
  var index := 1;
  while index < |a|
    invariant 0 < index <= |a|
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
  {
    break;
    if a[index] > a[i] {
      i := index;
    }
    index := index + 1;
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1201];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test2() {
var seqint0 : seq<int> := [6483, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test3() {
var seqint0 : seq<int> := [6484, 0, 0, 0, 0, 7719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5282];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 1236, -1201, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
