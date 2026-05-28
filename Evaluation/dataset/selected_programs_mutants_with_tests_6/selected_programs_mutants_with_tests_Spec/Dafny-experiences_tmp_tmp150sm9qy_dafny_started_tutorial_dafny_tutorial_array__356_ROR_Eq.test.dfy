// Dafny-experiences_tmp_tmp150sm9qy_dafny_started_tutorial_dafny_tutorial_array.dfy

method {:testEntry} FindMax(a: seq<int>) returns (i: int)
  requires |a| > 0
  ensures 0 <= i < |a|
  ensures forall k :: 0 <= k < |a| ==> a[k] <= a[i]
{
  i := 0;
  var index := 1;
  while index == |a|
    invariant 0 < index <= |a|
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
  {
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
var seqint0 : seq<int> := [0, 0];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test2() {
var seqint0 : seq<int> := [1236, -7719];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test3() {
var seqint0 : seq<int> := [7719, 6483];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test4() {
var seqint0 : seq<int> := [490, 0, 8855, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059, -2437];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
method {:test} Test5() {
var seqint0 : seq<int> := [5923, 6483, 7719];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FindMax(seqint0);
expect 0 <= r0 < |seqint0|;
expect forall k: int {:trigger seqint0[k]} :: 0 <= k < |seqint0| ==> seqint0[k] <= seqint0[r0];
}
