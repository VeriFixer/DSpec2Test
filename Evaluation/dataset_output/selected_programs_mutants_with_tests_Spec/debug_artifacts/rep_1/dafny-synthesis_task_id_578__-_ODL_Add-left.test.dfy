// dafny-synthesis_task_id_578.dfy

method {:testEntry} Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    returns (r: seq<int>)
  requires |s1| == |s2| && |s2| == |s3|
  ensures |r| == 3 * |s1|
  ensures forall i :: 0 <= i < |s1| ==> r[3 * i] == s1[i] && r[3 * i + 1] == s2[i] && r[3 * i + 2] == s3[i]
{
  r := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant forall k :: 0 <= k < i ==> r[3 * k] == s1[k] && r[3 * k + 1] == s2[k] && r[3 * k + 2] == s3[k]
  {
    r := [s1[i], s2[i], s3[i]];
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 1 - TIME: 2.9255437 s
