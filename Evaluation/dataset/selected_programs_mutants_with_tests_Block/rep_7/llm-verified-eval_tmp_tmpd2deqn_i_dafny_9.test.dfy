
method {:test} Test12() {
var seqint0 : seq<int> := [1235, 1235, 1236, 0, 4];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [-5748, 535, 9391, 0, 5, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 11.8456812 s