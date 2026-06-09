
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0, 0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 3 - TIME: 4.2031121 s