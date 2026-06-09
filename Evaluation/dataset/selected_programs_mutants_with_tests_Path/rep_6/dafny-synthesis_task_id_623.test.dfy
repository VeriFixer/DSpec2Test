
method {:test} Test5() {
var seqint0 : seq<int> := [977, 0, 1888];
expect 1578 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1578);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1578);
}

// REPEAT 6 - TIME: 81.0063995 s