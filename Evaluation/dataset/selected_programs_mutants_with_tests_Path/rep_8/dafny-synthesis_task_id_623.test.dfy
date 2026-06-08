
method {:test} Test7() {
var seqint0 : seq<int> := [2617];
expect 1580 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1580);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1580);
}

// REPEAT 8 - TIME: 105.5355637 s