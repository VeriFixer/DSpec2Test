
method {:test} Test11() {
var seqint0 : seq<int> := [131, 0];
var seqint1 : seq<int> := [129, 0];
var seqint2 : seq<int> := [128];
var seqint3 : seq<int> := [127];
var seqint4 : seq<int> := [126];
var seqint5 : seq<int> := [125];
var seqint6 : seq<int> := [124];
var seqint7 : seq<int> := [123];
var seqint8 : seq<int> := [122];
var seqint9 : seq<int> := [121];
var seqint10 : seq<int> := [120];
var seqint11 : seq<int> := [119];
var seqint12 : seq<int> := [118];
var seqint13 : seq<int> := [117];
var seqint14 : seq<int> := [116];
var seqint15 : seq<int> := [115];
var seqint16 : seq<int> := [114];
var seqint17 : seq<int> := [113];
var seqint18 : seq<int> := [112];
var seqint19 : seq<int> := [111];
var seqint20 : seq<int> := [110];
var seqint21 : seq<int> := [109];
var seqint22 : seq<int> := [108];
var seqint23 : seq<int> := [107];
var seqint24 : seq<int> := [106];
var seqint25 : seq<int> := [105];
var seqint26 : seq<int> := [104];
var seqint27 : seq<int> := [103];
var seqint28 : seq<int> := [102];
var seqint29 : seq<int> := [101];
var seqint30 : seq<int> := [100];
var seqint31 : seq<int> := [99];
var seqint32 : seq<int> := [97];
var seqint33 : seq<int> := [96];
var seqint34 : seq<int> := [95];
var seqint35 : seq<int> := [94];
var seqint36 : seq<int> := [93];
var seqint37 : seq<int> := [92];
var seqint38 : seq<int> := [91];
var seqint39 : seq<int> := [90];
var seqint40 : seq<int> := [89, 0];
var seqint41 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 8.3578994 s