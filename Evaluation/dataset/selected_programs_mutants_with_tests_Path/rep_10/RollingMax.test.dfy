
method {:test} Test18() {
var seqint0 : seq<int> := [7563, 8098, 8098, 0, 8098, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [2662, 0, 0, 8945, 0, 0, 0, 0, 8945, 0, 0, 0, 0, 0, 5948, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8945, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 10 - TIME: 158.5195759 s