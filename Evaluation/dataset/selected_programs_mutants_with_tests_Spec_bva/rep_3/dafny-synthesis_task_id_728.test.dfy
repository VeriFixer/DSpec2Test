
method {:test} Test14() {
var seqint0 : seq<int> := [-1201, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6569];
var seqint1 : seq<int> := [2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 3 - TIME: 8.8309541 s