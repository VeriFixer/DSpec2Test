
method {:test} Test4() {
var seqint0 : seq<int> := [-5282, 0, 0, 0];
var seqint1 : seq<int> := [7719, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 5 - TIME: 6.6353053 s