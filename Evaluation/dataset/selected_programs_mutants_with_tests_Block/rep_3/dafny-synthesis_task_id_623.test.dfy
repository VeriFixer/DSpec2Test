
method {:test} Test2() {
var seqint0 : seq<int> := [2437, 0];
expect 611 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 611);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 611);
}

// REPEAT 3 - TIME: 4.0858126 s