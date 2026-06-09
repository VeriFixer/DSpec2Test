
method {:test} Test12() {
var seqint0 : seq<int> := [-533, 0, 609, 0, 0, 609, 609, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [861, 0, 0, 0, 1142, 1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 607, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 103.6904851 s