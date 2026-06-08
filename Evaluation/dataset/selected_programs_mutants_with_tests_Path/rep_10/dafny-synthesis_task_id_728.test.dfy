
method {:test} Test9() {
var seqint0 : seq<int> := [-861, 0, 3025, 0, 0, 0, 0, 0, -7133, 0, 0, 1682, 7485];
var seqint1 : seq<int> := [1142, 0, 5920, 0, 0, 0, 0, 0, 8456, 0, 0, 2997, 2240];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 10 - TIME: 104.1063934 s