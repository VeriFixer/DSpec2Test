
method {:test} Test30() {
var seqint0 : seq<int> := [-4617, -7619, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test31() {
var seqint0 : seq<int> := [29, 43, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37, 0, 33, 41, 39];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 50.9290368 s