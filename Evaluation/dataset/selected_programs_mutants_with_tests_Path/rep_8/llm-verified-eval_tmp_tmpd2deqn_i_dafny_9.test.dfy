
method {:test} Test14() {
var seqint0 : seq<int> := [2178, 8098, 8098, 0, 0, 0, 0, 8098, 0, 0, 0, -847, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [-4144, 0, 0, 535, 0, 0, 0, 0, 0, 0, 0, 0, 535, 0, 0, 0, -439, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 78.3620164 s