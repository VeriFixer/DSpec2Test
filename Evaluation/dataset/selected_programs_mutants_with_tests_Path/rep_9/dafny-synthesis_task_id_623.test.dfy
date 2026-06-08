
method {:test} Test8() {
var seqint0 : seq<int> := [1653, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1581 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1581);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1581);
}

// REPEAT 9 - TIME: 121.1177845 s