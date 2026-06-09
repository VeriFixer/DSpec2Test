
method {:test} Test9() {
var seqint0 : seq<int> := [3961, 0, 0, 0];
expect 1582 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1582);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1582);
}

// REPEAT 10 - TIME: 151.3933067 s