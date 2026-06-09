
method {:test} Test22() {
var seqint0 : seq<int> := [-1136];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test23() {
var seqint0 : seq<int> := [13, 0, 7];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 39.0918327 s