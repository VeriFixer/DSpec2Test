
method {:test} Test16() {
var seqint0 : seq<int> := [-4669, 0, 0, 1235, 1236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 8, 0, 0, 0, 12, 14];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [1796, 3033];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 13.8332155 s