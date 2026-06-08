
method {:test} Test7() {
var seqint0 : seq<int> := [0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 10, 0, 0, 0, 0, 14, 0, 16, 0, 0, 0, 0, 0, 18];
expect 616 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 616);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 616);
}

// REPEAT 8 - TIME: 10.040689 s