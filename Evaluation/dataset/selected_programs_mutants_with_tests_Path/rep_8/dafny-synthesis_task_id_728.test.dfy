
method {:test} Test7() {
var seqint0 : seq<int> := [5244, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1682, 0, 3025, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -861];
var seqint1 : seq<int> := [609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2997, 0, 5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 8 - TIME: 86.7117925 s