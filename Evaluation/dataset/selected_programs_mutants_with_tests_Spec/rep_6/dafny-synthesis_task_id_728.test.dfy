
method {:test} Test5() {
var seqint0 : seq<int> := [4679, 8855];
var seqint1 : seq<int> := [974, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AddLists(seqint0, seqint1);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqint0[i] + seqint1[i];
}

// REPEAT 6 - TIME: 7.7357608 s