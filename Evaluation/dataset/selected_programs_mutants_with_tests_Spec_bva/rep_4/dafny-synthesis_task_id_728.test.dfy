
method {:test} Test15() {
var seqint0 : seq<int> := [8098, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 449];
var seqint1 : seq<int> := [-2245, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059, 1833];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 4 - TIME: 9.4563185 s