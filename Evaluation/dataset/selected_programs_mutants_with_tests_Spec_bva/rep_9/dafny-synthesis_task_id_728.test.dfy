
method {:test} Test20() {
var seqint0 : seq<int> := [2275, 0, 0, 0, 0, 974, 535, 609, 1796, 6283];
var seqint1 : seq<int> := [2446, 0, 0, 0, 0, 1888, 5920, 5853, 8365, 2997];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 13.8532818 s