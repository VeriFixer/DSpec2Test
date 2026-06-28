// dafny-synthesis_task_id_743.dfy

method {:testEntry} RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
  var rotated: seq<int> := [];
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant |rotated| == i
    invariant forall k :: 0 <= k < i ==> rotated[k] == l[(k - n + |l|) % |l|]
  {
    rotated := rotated + [l[i - n + |l|]];
  }
  return rotated;
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateRight(seqint0, 0);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i - 0 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.6781392 s
