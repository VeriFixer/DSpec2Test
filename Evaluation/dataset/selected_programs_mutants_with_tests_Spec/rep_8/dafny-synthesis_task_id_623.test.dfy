
method {:test} Test7() {
var seqint0 : seq<int> := [0, 8945, 1236];
expect 7072 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7072);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7072);
}

// REPEAT 8 - TIME: 8.9806452 s