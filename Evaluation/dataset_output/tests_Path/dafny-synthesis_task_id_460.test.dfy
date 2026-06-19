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

// REPEAT 1 - TIME: 10.0944647 s

method {:test} Test1() {
var seqint0 : seq<int> := [25];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 2 - TIME: 16.7088955 s

method {:test} Test2() {
var seqint0 : seq<int> := [31, 0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 24.122714 s

method {:test} Test3() {
var seqint0 : seq<int> := [27, 0, 0];
var seqint1 : seq<int> := [26];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 33.4529908 s

method {:test} Test4() {
var seqint0 : seq<int> := [43, 0, 0, 0];
var seqint1 : seq<int> := [45, 0];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 5 - TIME: 41.5392234 s

method {:test} Test5() {
var seqint0 : seq<int> := [30, 0, 0, 0, 0];
var seqint1 : seq<int> := [32, 0, 0];
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
var seqint22 : seq<int> := [];
var seqint23 : seq<int> := [64];
var seqint24 : seq<int> := [65];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 48.6436018 s

method {:test} Test6() {
var seqint0 : seq<int> := [52, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [51, 0, 0, 0];
var seqint2 : seq<int> := [50, 0];
var seqint3 : seq<int> := [49];
var seqint4 : seq<int> := [48];
var seqint5 : seq<int> := [47];
var seqint6 : seq<int> := [46];
var seqint7 : seq<int> := [44];
var seqint8 : seq<int> := [42];
var seqint9 : seq<int> := [41];
var seqint10 : seq<int> := [40];
var seqint11 : seq<int> := [39];
var seqint12 : seq<int> := [38];
var seqint13 : seq<int> := [37];
var seqint14 : seq<int> := [36];
var seqint15 : seq<int> := [35];
var seqint16 : seq<int> := [34];
var seqint17 : seq<int> := [60];
var seqint18 : seq<int> := [59];
var seqint19 : seq<int> := [58];
var seqint20 : seq<int> := [57];
var seqint21 : seq<int> := [56];
var seqint22 : seq<int> := [55];
var seqint23 : seq<int> := [54, 0];
var seqint24 : seq<int> := [53, 0];
var seqint25 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 56.8848606 s

method {:test} Test7() {
var seqint0 : seq<int> := [189, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [188, 0, 0, 0, 0];
var seqint2 : seq<int> := [187, 0, 0];
var seqint3 : seq<int> := [186, 0];
var seqint4 : seq<int> := [185, 0];
var seqint5 : seq<int> := [184, 0];
var seqint6 : seq<int> := [183, 0];
var seqint7 : seq<int> := [182, 0];
var seqint8 : seq<int> := [181, 0];
var seqint9 : seq<int> := [180, 0];
var seqint10 : seq<int> := [179, 0];
var seqint11 : seq<int> := [178, 0];
var seqint12 : seq<int> := [177, 0];
var seqint13 : seq<int> := [176, 0];
var seqint14 : seq<int> := [175, 0];
var seqint15 : seq<int> := [174, 0];
var seqint16 : seq<int> := [173, 0];
var seqint17 : seq<int> := [172, 0];
var seqint18 : seq<int> := [171, 0];
var seqint19 : seq<int> := [170, 0];
var seqint20 : seq<int> := [169, 0];
var seqint21 : seq<int> := [168, 0];
var seqint22 : seq<int> := [167, 0];
var seqint23 : seq<int> := [191, 0, 0];
var seqint24 : seq<int> := [190, 0, 0];
var seqint25 : seq<int> := [192];
var seqint26 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 66.9829252 s

method {:test} Test8() {
var seqint0 : seq<int> := [279, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [278, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [277, 0, 0, 0];
var seqint3 : seq<int> := [276, 0, 0];
var seqint4 : seq<int> := [275, 0, 0];
var seqint5 : seq<int> := [274, 0, 0];
var seqint6 : seq<int> := [273, 0, 0];
var seqint7 : seq<int> := [272, 0, 0];
var seqint8 : seq<int> := [271, 0, 0];
var seqint9 : seq<int> := [270, 0, 0];
var seqint10 : seq<int> := [269, 0, 0];
var seqint11 : seq<int> := [268, 0, 0];
var seqint12 : seq<int> := [267, 0, 0];
var seqint13 : seq<int> := [266, 0, 0];
var seqint14 : seq<int> := [265, 0, 0];
var seqint15 : seq<int> := [264, 0, 0];
var seqint16 : seq<int> := [263, 0, 0];
var seqint17 : seq<int> := [262, 0, 0];
var seqint18 : seq<int> := [261, 0, 0];
var seqint19 : seq<int> := [260, 0, 0];
var seqint20 : seq<int> := [259, 0, 0];
var seqint21 : seq<int> := [258, 0, 0];
var seqint22 : seq<int> := [257, 0, 0];
var seqint23 : seq<int> := [281, 0, 0, 0];
var seqint24 : seq<int> := [280, 0, 0, 0];
var seqint25 : seq<int> := [282, 0];
var seqint26 : seq<int> := [283];
var seqint27 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 82.798348 s

method {:test} Test9() {
var seqint0 : seq<int> := [396, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [395, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [394, 0, 0, 0, 0];
var seqint3 : seq<int> := [393, 0, 0, 0];
var seqint4 : seq<int> := [392, 0, 0, 0];
var seqint5 : seq<int> := [391, 0, 0, 0];
var seqint6 : seq<int> := [390, 0, 0, 0];
var seqint7 : seq<int> := [389, 0, 0, 0];
var seqint8 : seq<int> := [388, 0, 0, 0];
var seqint9 : seq<int> := [387, 0, 0, 0];
var seqint10 : seq<int> := [386, 0, 0, 0];
var seqint11 : seq<int> := [385, 0, 0, 0];
var seqint12 : seq<int> := [384, 0, 0, 0];
var seqint13 : seq<int> := [383, 0, 0, 0];
var seqint14 : seq<int> := [382, 0, 0, 0];
var seqint15 : seq<int> := [381, 0, 0, 0];
var seqint16 : seq<int> := [380, 0, 0, 0];
var seqint17 : seq<int> := [379, 0, 0, 0];
var seqint18 : seq<int> := [378, 0, 0, 0];
var seqint19 : seq<int> := [377, 0, 0, 0];
var seqint20 : seq<int> := [376, 0, 0, 0];
var seqint21 : seq<int> := [375, 0, 0, 0];
var seqint22 : seq<int> := [374, 0, 0, 0];
var seqint23 : seq<int> := [398, 0, 0, 0, 0];
var seqint24 : seq<int> := [397, 0, 0, 0, 0];
var seqint25 : seq<int> := [399, 0, 0];
var seqint26 : seq<int> := [400, 0];
var seqint27 : seq<int> := [401];
var seqint28 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 100.2109169 s
