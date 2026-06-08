
method {:test} Test5() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 6 - TIME: 64.5724022 s