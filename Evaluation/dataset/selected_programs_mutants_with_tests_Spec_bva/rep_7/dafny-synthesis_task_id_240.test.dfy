
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 165];
var seqint1 : seq<int> := [165, 0, 0, 9, 0, 17];
expect |seqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ReplaceLastElement(seqint0, seqint1);
expect |r0| == |seqint0| - 1 + |seqint1|;
expect forall i :: 0 <= i < |seqint0| - 1 ==> r0[i] == seqint0[i];
expect forall i :: |seqint0| - 1 <= i < |r0| ==> r0[i] == seqint1[i - |seqint0| + 1];
}

// REPEAT 7 - TIME: 12.9874552 s