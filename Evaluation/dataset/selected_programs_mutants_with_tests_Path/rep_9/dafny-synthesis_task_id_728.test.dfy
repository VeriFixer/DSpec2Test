
method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 254, 2245];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 281, 5853];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 9 - TIME: 116.8503789 s