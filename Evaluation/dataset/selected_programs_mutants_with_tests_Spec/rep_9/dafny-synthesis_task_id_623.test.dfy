
method {:test} Test8() {
var seqint0 : seq<int> := [1594, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect 7073 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7073);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7073);
}

// REPEAT 9 - TIME: 11.2614339 s