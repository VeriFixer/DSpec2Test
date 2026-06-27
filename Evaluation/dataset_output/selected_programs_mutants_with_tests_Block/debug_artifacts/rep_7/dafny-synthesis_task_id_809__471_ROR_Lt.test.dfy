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
    if a[i] < b[i] {
      result := false;
      break;
    }
  }
}

method {:test} Test6() {
var seqint0 : seq<int> := [2283, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1797, 0, 0, 0, 0, -6418];
var seqint1 : seq<int> := [2282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 2437];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 7 - TIME: 9.671303 s
