
method {:test} Test6() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [];
var seqint9 : seq<int> := [];
var seqint10 : seq<int> := [];
var seqint11 : seq<int> := [];
var seqint12 : seq<int> := [];
var seqint13 : seq<int> := [];
var seqint14 : seq<int> := [];
var seqint15 : seq<int> := [];
var seqint16 : seq<int> := [];
var seqint17 : seq<int> := [];
var seqint18 : seq<int> := [];
var seqint19 : seq<int> := [];
var seqint20 : seq<int> := [];
var seqint21 : seq<int> := [];
var seqint22 : seq<int> := [];
var seqint23 : seq<int> := [];
var seqint24 : seq<int> := [];
var seqint25 : seq<int> := [0];
var seqint26 : seq<int> := [];
var seqint27 : seq<int> := [];
var seqint28 : seq<int> := [];
var seqint29 : seq<int> := [];
var seqint30 : seq<int> := [];
var seqint31 : seq<int> := [];
var seqint32 : seq<int> := [];
var seqint33 : seq<int> := [];
var seqint34 : seq<int> := [];
var seqint35 : seq<int> := [];
var seqint36 : seq<int> := [];
var seqint37 : seq<int> := [];
var seqint38 : seq<int> := [];
var seqint39 : seq<int> := [0];
var seqint40 : seq<int> := [];
var seqint41 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MinLengthSublist(seqseqint0);
expect r0 in seqseqint0;
expect forall sublist :: sublist in seqseqint0 ==> |r0| <= |sublist|;
}

// REPEAT 7 - TIME: 9.0944046 s