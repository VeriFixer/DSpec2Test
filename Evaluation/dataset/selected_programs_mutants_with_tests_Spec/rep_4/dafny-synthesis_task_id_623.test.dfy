
method {:test} Test3() {
var seqint0 : seq<int> := [0, 8855, 0, 0, 0, 0, 0, 0, 0, 0];
expect 7068 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7068);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7068);
}

// REPEAT 4 - TIME: 7.0082451 s