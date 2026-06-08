
method {:test} Test13() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [0, 0, 0, 0];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [];
var seqint9 : seq<int> := [];
var seqint10 : seq<int> := [];
var seqint11 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 6 - TIME: 10.6271776 s