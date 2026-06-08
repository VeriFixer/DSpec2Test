
method {:test} Test7() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [0, 0];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 8 - TIME: 9.5523747 s