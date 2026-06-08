
method {:test} Test24() {
var seqint0 : seq<int> := [8084, 0, 7916, 0, 0, 0, 0, 7756, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2512, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6083, 0, 0, 7223, 0, 0, 0, 0, 0, 267];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test25() {
var seqint0 : seq<int> := [16, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 20, 22];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 46.5001845 s