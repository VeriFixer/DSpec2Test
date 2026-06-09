
method {:test} Test12() {
var seqint0 : seq<int> := [228, 0, 0];
var seqint1 : seq<int> := [227, 0, 0];
var seqint2 : seq<int> := [225, 0];
var seqint3 : seq<int> := [224, 0];
var seqint4 : seq<int> := [223, 0];
var seqint5 : seq<int> := [222, 0];
var seqint6 : seq<int> := [221, 0];
var seqint7 : seq<int> := [220, 0];
var seqint8 : seq<int> := [219, 0];
var seqint9 : seq<int> := [218, 0];
var seqint10 : seq<int> := [217, 0];
var seqint11 : seq<int> := [216, 0];
var seqint12 : seq<int> := [215, 0];
var seqint13 : seq<int> := [214, 0];
var seqint14 : seq<int> := [213, 0];
var seqint15 : seq<int> := [254, 0];
var seqint16 : seq<int> := [253, 0];
var seqint17 : seq<int> := [252, 0];
var seqint18 : seq<int> := [251, 0];
var seqint19 : seq<int> := [250, 0];
var seqint20 : seq<int> := [249, 0];
var seqint21 : seq<int> := [248, 0];
var seqint22 : seq<int> := [247, 0];
var seqint23 : seq<int> := [246, 0];
var seqint24 : seq<int> := [245, 0];
var seqint25 : seq<int> := [244, 0];
var seqint26 : seq<int> := [243, 0];
var seqint27 : seq<int> := [242, 0];
var seqint28 : seq<int> := [241, 0];
var seqint29 : seq<int> := [240, 0];
var seqint30 : seq<int> := [239, 0];
var seqint31 : seq<int> := [238, 0];
var seqint32 : seq<int> := [237, 0];
var seqint33 : seq<int> := [236, 0];
var seqint34 : seq<int> := [235, 0];
var seqint35 : seq<int> := [234, 0];
var seqint36 : seq<int> := [233, 0];
var seqint37 : seq<int> := [232, 0];
var seqint38 : seq<int> := [231, 0];
var seqint39 : seq<int> := [230, 0];
var seqint40 : seq<int> := [229, 0, 0];
var seqint41 : seq<int> := [255];
var seqint42 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 9.5674491 s