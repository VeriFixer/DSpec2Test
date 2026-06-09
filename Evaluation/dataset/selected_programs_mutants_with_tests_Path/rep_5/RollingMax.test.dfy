
method {:test} Test8() {
var seqint0 : seq<int> := [-7489, 0, 0, 609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 609, 0, 0, 0, 609, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [-2245, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 5853, 0, 0, 0, 0, 5853, 0, 4711];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 73.2302367 s