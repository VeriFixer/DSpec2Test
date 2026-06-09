
method {:test} Test10() {
var seqint0 : seq<int> := [267, 0, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 0, 8365, 0, 0, 7223];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [-7489, 0, 0, 609, 0, 0, 0, 609, 0, 0, 0, 0, 0, 0, 0, 609, -533, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 53.8546767 s