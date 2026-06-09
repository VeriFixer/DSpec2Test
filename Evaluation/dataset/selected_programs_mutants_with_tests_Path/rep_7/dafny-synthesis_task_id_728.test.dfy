
method {:test} Test6() {
var seqint0 : seq<int> := [5385, 0, -6956, 0, 0, 0, 0, 0, 0, 0, 0, -3286];
var seqint1 : seq<int> := [535, 0, 8098, 0, 0, 0, 0, 0, 0, 0, 0, 6283];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 86.4124304 s