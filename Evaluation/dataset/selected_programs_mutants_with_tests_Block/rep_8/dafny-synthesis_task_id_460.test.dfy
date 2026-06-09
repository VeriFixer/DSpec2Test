
method {:test} Test7() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0];
var seqint39 : seq<int> := [0];
var seqint40 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 9.9117037 s