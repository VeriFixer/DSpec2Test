
method {:test} Test6() {
var seqint0 : seq<int> := [1236, 0, 0, 10, 0, 14];
var seqint1 : seq<int> := [6862, 16, 0, 6, 0, 12];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 7 - TIME: 8.5929114 s