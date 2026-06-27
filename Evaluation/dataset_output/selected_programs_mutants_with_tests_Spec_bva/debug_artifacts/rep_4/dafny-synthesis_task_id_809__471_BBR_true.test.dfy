// dafny-synthesis_task_id_809.dfy

method {:testEntry} IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  requires |a| == |b|
  ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
  ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{
  result := true;
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant result <==> forall k :: 0 <= k < i ==> a[k] > b[k]
    invariant !result <==> exists k :: 0 <= k < i && a[k] <= b[k]
  {
    if true {
      result := false;
      break;
    }
  }
}

method {:test} Test24() {
var seqint0 : seq<int> := [591, 0, 0, 0, 0, 0, 0, 4679, 0, 0, 2241, 0, 2276, 0, 0, 6284, 0, 0, 0, 0, 0, 5904, 0, 1324];
var seqint1 : seq<int> := [590, 0, 0, 0, 0, 0, 0, 4678, 0, 0, 2240, 0, 2275, 0, 0, 6283, 0, 0, 0, 0, 0, 5903, 0, 1323];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test25() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, -8365, 0, 0, 12, 0, 0, 17, 0, 0, -2437, 0];
var seqint1 : seq<int> := [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6083, 0, 0, 15, 0, 0, 0, 0, 19, 6418, 23];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 4 - TIME: 14.7720181 s
