method {:testEntry} GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
{
    result := [];
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == lst[j][0]
    {
        result := result + [lst[i][0]];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 1 - TIME: 13.7987998 s

method {:test} Test1() {
var seqint0 : seq<int> := [26];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 2 - TIME: 23.8882869 s

method {:test} Test2() {
var seqint0 : seq<int> := [32, 0];
var seqint1 : seq<int> := [34];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 35.0951408 s

method {:test} Test3() {
var seqint0 : seq<int> := [27, 0, 0];
var seqint1 : seq<int> := [25, 0];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 46.3046929 s

method {:test} Test4() {
var seqint0 : seq<int> := [30, 0, 0, 0];
var seqint1 : seq<int> := [31, 0, 0];
var seqint2 : seq<int> := [29];
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
var seqint22 : seq<int> := [51];
var seqint23 : seq<int> := [52];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 5 - TIME: 58.4738394 s

method {:test} Test5() {
var seqint0 : seq<int> := [55, 0, 0, 0, 0];
var seqint1 : seq<int> := [54, 0, 0, 0];
var seqint2 : seq<int> := [53, 0];
var seqint3 : seq<int> := [50];
var seqint4 : seq<int> := [49];
var seqint5 : seq<int> := [48];
var seqint6 : seq<int> := [47];
var seqint7 : seq<int> := [46];
var seqint8 : seq<int> := [45];
var seqint9 : seq<int> := [44];
var seqint10 : seq<int> := [43];
var seqint11 : seq<int> := [42];
var seqint12 : seq<int> := [41];
var seqint13 : seq<int> := [40];
var seqint14 : seq<int> := [39];
var seqint15 : seq<int> := [38];
var seqint16 : seq<int> := [36];
var seqint17 : seq<int> := [59];
var seqint18 : seq<int> := [58];
var seqint19 : seq<int> := [57];
var seqint20 : seq<int> := [56];
var seqint21 : seq<int> := [61];
var seqint22 : seq<int> := [60, 0];
var seqint23 : seq<int> := [62, 0];
var seqint24 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 72.2808 s

method {:test} Test6() {
var seqint0 : seq<int> := [172, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [171, 0, 0, 0, 0];
var seqint2 : seq<int> := [170, 0, 0];
var seqint3 : seq<int> := [169, 0];
var seqint4 : seq<int> := [168, 0];
var seqint5 : seq<int> := [167, 0];
var seqint6 : seq<int> := [166, 0];
var seqint7 : seq<int> := [165, 0];
var seqint8 : seq<int> := [164, 0];
var seqint9 : seq<int> := [163, 0];
var seqint10 : seq<int> := [162, 0];
var seqint11 : seq<int> := [161, 0];
var seqint12 : seq<int> := [160, 0];
var seqint13 : seq<int> := [159, 0];
var seqint14 : seq<int> := [158, 0];
var seqint15 : seq<int> := [157, 0];
var seqint16 : seq<int> := [156, 0];
var seqint17 : seq<int> := [179, 0];
var seqint18 : seq<int> := [178, 0];
var seqint19 : seq<int> := [177, 0];
var seqint20 : seq<int> := [176, 0];
var seqint21 : seq<int> := [175, 0];
var seqint22 : seq<int> := [174, 0, 0];
var seqint23 : seq<int> := [173, 0, 0];
var seqint24 : seq<int> := [180];
var seqint25 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 88.7990957 s

method {:test} Test7() {
var seqint0 : seq<int> := [257, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [256, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [255, 0, 0, 0];
var seqint3 : seq<int> := [254, 0, 0];
var seqint4 : seq<int> := [253, 0, 0];
var seqint5 : seq<int> := [252, 0, 0];
var seqint6 : seq<int> := [251, 0, 0];
var seqint7 : seq<int> := [250, 0, 0];
var seqint8 : seq<int> := [249, 0, 0];
var seqint9 : seq<int> := [248, 0, 0];
var seqint10 : seq<int> := [247, 0, 0];
var seqint11 : seq<int> := [246, 0, 0];
var seqint12 : seq<int> := [245, 0, 0];
var seqint13 : seq<int> := [244, 0, 0];
var seqint14 : seq<int> := [243, 0, 0];
var seqint15 : seq<int> := [242, 0, 0];
var seqint16 : seq<int> := [241, 0, 0];
var seqint17 : seq<int> := [264, 0, 0];
var seqint18 : seq<int> := [263, 0, 0];
var seqint19 : seq<int> := [262, 0, 0];
var seqint20 : seq<int> := [261, 0, 0];
var seqint21 : seq<int> := [260, 0, 0];
var seqint22 : seq<int> := [259, 0, 0, 0];
var seqint23 : seq<int> := [258, 0, 0, 0];
var seqint24 : seq<int> := [265, 0];
var seqint25 : seq<int> := [266];
var seqint26 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 108.6574477 s

method {:test} Test8() {
var seqint0 : seq<int> := [378, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [377, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [376, 0, 0, 0, 0];
var seqint3 : seq<int> := [375, 0, 0, 0];
var seqint4 : seq<int> := [374, 0, 0, 0];
var seqint5 : seq<int> := [373, 0, 0, 0];
var seqint6 : seq<int> := [372, 0, 0, 0];
var seqint7 : seq<int> := [371, 0, 0, 0];
var seqint8 : seq<int> := [370, 0, 0, 0];
var seqint9 : seq<int> := [369, 0, 0, 0];
var seqint10 : seq<int> := [368, 0, 0, 0];
var seqint11 : seq<int> := [367, 0, 0, 0];
var seqint12 : seq<int> := [366, 0, 0, 0];
var seqint13 : seq<int> := [365, 0, 0, 0];
var seqint14 : seq<int> := [364, 0, 0, 0];
var seqint15 : seq<int> := [363, 0, 0, 0];
var seqint16 : seq<int> := [362, 0, 0, 0];
var seqint17 : seq<int> := [361, 0, 0, 0];
var seqint18 : seq<int> := [360, 0, 0, 0];
var seqint19 : seq<int> := [359, 0, 0, 0];
var seqint20 : seq<int> := [358, 0, 0, 0];
var seqint21 : seq<int> := [357, 0, 0, 0];
var seqint22 : seq<int> := [356, 0, 0, 0, 0];
var seqint23 : seq<int> := [355, 0, 0, 0, 0];
var seqint24 : seq<int> := [354, 0, 0];
var seqint25 : seq<int> := [379, 0];
var seqint26 : seq<int> := [380];
var seqint27 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 140.4099655 s

method {:test} Test9() {
var seqint0 : seq<int> := [518, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [517, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [516, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [515, 0, 0, 0, 0];
var seqint4 : seq<int> := [514, 0, 0, 0, 0];
var seqint5 : seq<int> := [513, 0, 0, 0, 0];
var seqint6 : seq<int> := [512, 0, 0, 0, 0];
var seqint7 : seq<int> := [511, 0, 0, 0, 0];
var seqint8 : seq<int> := [510, 0, 0, 0, 0];
var seqint9 : seq<int> := [509, 0, 0, 0, 0];
var seqint10 : seq<int> := [508, 0, 0, 0, 0];
var seqint11 : seq<int> := [507, 0, 0, 0, 0];
var seqint12 : seq<int> := [506, 0, 0, 0, 0];
var seqint13 : seq<int> := [505, 0, 0, 0, 0];
var seqint14 : seq<int> := [504, 0, 0, 0, 0];
var seqint15 : seq<int> := [503, 0, 0, 0, 0];
var seqint16 : seq<int> := [502, 0, 0, 0, 0];
var seqint17 : seq<int> := [501, 0, 0, 0, 0];
var seqint18 : seq<int> := [500, 0, 0, 0, 0];
var seqint19 : seq<int> := [499, 0, 0, 0, 0];
var seqint20 : seq<int> := [498, 0, 0, 0, 0];
var seqint21 : seq<int> := [497, 0, 0, 0, 0];
var seqint22 : seq<int> := [496, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [495, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [494, 0, 0, 0];
var seqint25 : seq<int> := [519, 0, 0];
var seqint26 : seq<int> := [520, 0];
var seqint27 : seq<int> := [521];
var seqint28 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 171.1314695 s
