
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 0, 0, 0, 0, 0, 609, 0, 8365];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 5385, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8098, 0, 0, 0, 0, 0, 0, 449, 0, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 4 - TIME: 5.5358594 s