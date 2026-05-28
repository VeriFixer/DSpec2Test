method {:testEntry} FindMax(a: seq<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires |a| > 0
  ensures 0<= i < |a|
  ensures forall k :: 0 <= k < |a| ==> a[k] <= a[i]
{
  // Fill in the body that calculates the INDEX of the maximum.
  i := 0;
  var index := 1;
  while index < |a|
    invariant 0 < index <= |a|
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
  {
    if a[index] > a[i] {i:= index;}
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
