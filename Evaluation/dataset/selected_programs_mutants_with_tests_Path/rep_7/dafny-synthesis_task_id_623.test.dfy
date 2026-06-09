
method {:test} Test6() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 1];
expect 1579 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1579);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1579);
}

// REPEAT 7 - TIME: 95.7557619 s