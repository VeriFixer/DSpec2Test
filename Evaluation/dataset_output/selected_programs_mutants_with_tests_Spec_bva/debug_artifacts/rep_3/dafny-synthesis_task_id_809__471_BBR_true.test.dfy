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

method {:test} Test22() {
var seqint0 : seq<int> := [8221, 1888, 0, 0, 1324, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5905];
var seqint1 : seq<int> := [8220, 1887, 0, 0, 1323, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5904];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test23() {
var seqint0 : seq<int> := [0, 0, 0, -1236, 0, 0, 0, 0, 7059, 0, 9, 0];
var seqint1 : seq<int> := [0, 0, 0, 1201, 0, 0, 0, 7, 8855, 0, 11, 13];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 3 - TIME: 18.3310899 s
