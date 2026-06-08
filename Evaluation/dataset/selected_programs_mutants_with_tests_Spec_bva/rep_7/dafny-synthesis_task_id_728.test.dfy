
method {:test} Test18() {
var seqint0 : seq<int> := [6283, 0, 0, 0, 0, 1796, 0, 1236, 449];
var seqint1 : seq<int> := [-3285, 0, 0, 0, 0, 6569, 0, 1201, 160];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 12.307291 s