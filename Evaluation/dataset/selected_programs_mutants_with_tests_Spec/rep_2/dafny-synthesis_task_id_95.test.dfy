
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 2 - TIME: 3.6345583 s