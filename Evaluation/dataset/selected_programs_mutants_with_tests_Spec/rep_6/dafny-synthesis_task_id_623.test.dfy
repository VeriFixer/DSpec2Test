
method {:test} Test5() {
var seqint0 : seq<int> := [7066, 0, 5259];
expect 7070 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PowerOfListElements(seqint0, 7070);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == Power(seqint0[i], 7070);
}

// REPEAT 6 - TIME: 8.8017152 s