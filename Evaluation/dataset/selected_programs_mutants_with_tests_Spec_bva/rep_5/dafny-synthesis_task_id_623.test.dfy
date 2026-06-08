
method {:test} Test15() {
var seqint0 : seq<int> := [609, 0, 1236];
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 104);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 104);
}

// REPEAT 5 - TIME: 12.344136 s