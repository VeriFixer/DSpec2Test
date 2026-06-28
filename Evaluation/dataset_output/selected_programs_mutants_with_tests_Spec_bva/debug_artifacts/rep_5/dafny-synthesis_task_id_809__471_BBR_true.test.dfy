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

method {:test} Test26() {
var seqint0 : seq<int> := [3153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7854, 0, 6927, 0, 0, 2332, 0, 4771, 0, 2113, 1650, 6703];
var seqint1 : seq<int> := [3152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7853, 0, 6926, 0, 0, 2331, 0, 4770, 0, 2112, 1649, 6702];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test27() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -6569, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, -1201, 0, 0, 0, 20, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236, 0, 0, 0, 0, 16];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 5 - TIME: 21.6196714 s
