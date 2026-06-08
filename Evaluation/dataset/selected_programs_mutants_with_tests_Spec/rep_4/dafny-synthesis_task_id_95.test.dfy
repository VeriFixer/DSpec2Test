
method {:test} Test3() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 4 - TIME: 5.6523812 s