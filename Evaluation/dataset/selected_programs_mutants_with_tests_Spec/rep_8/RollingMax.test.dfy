
method {:test} Test14() {
var seqint0 : seq<int> := [787, -1201, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7129, 1236, 0, 0, 0, 0, 0, 0, 0, -1046];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [13, 0, 10];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 28.5425787 s