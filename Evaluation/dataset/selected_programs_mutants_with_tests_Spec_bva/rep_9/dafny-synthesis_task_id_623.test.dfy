
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 2211, 1];
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 108);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 108);
}

// REPEAT 9 - TIME: 14.1327791 s