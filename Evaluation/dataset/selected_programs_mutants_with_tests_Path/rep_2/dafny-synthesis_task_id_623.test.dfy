
method {:test} Test1() {
var seqint0 : seq<int> := [8855];
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1);
}

// REPEAT 2 - TIME: 24.6037597 s