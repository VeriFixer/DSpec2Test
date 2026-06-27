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
    if a[i] == b[i] {
      result := false;
      break;
    }
  }
}

method {:test} Test12() {
var seqint0 : seq<int> := [974, 0, 536, 0, 8099, 1142, 0, 0];
var seqint1 : seq<int> := [973, 0, 535, 0, 8098, 1141, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test13() {
var seqint0 : seq<int> := [7677, 0, 0, 0, 610, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6083];
var seqint1 : seq<int> := [2997, 0, 0, 0, 609, 0, 5852, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8365];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 7 - TIME: 1230.447471 s
