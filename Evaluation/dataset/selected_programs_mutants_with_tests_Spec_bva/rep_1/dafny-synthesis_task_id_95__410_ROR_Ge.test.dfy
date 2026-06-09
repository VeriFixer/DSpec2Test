// dafny-synthesis_task_id_95.dfy

method {:testEntry} SmallestListLength(s: seq<seq<int>>) returns (v: int)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
  ensures exists i :: 0 <= i < |s| && v == |s[i]|
{
  v := |s[0]|;
  for i := 1 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> v <= |s[k]|
    invariant exists k :: 0 <= k < i && v == |s[k]|
  {
    if |s[i]| >= v {
      v := |s[i]|;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}
method {:test} Test2() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 1 - TIME: 4.6815158 s
