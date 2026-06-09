
method {:test} Test4() {
var seqint0 : seq<int> := [1, 0, 2331];
expect 1577 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 1577);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 1577);
}

// REPEAT 5 - TIME: 64.8480275 s