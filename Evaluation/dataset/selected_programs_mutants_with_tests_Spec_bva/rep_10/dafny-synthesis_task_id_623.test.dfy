
method {:test} Test20() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1314, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1];
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 109);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 109);
}

// REPEAT 10 - TIME: 16.5213583 s