
method {:test} Test6() {
var seqint0 : seq<int> := [1796, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 1187];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [3705, 4679, 0, 0, 0, 0, 0, 4679, 0, 0, 0, 0, 0, 0, 4679, 0, 0, 0, 0, 2791];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 4 - TIME: 69.3479659 s