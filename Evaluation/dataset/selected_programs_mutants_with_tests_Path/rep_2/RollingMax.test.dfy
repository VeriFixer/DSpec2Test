
method {:test} Test2() {
var seqint0 : seq<int> := [5572, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 5853, 0, 0, 5853];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [8365, 0, 0, 0, 0, 0, 0, 8365, 0, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2082];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 2 - TIME: 25.8673857 s