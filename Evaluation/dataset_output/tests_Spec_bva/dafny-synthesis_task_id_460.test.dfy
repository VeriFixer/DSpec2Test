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
method {:test} Test1() {
var seqseqint0 : seq<seq<int>> := [];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}
method {:test} Test3() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 1 - TIME: 9.7195718 s

method {:test} Test10() {
var seqint0 : seq<int> := [25];
var seqint1 : seq<int> := [26];
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
var seqint12 : seq<int> := [31];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 2 - TIME: 10.8796047 s

method {:test} Test11() {
var seqint0 : seq<int> := [39, 0];
var seqint1 : seq<int> := [38, 0];
var seqint2 : seq<int> := [36];
var seqint3 : seq<int> := [35];
var seqint4 : seq<int> := [34];
var seqint5 : seq<int> := [33];
var seqint6 : seq<int> := [32];
var seqint7 : seq<int> := [30];
var seqint8 : seq<int> := [29];
var seqint9 : seq<int> := [43];
var seqint10 : seq<int> := [41];
var seqint11 : seq<int> := [40];
var seqint12 : seq<int> := [28, 0];
var seqint13 : seq<int> := [64];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 11.8743907 s

method {:test} Test12() {
var seqint0 : seq<int> := [105, 0, 0];
var seqint1 : seq<int> := [103, 0, 0];
var seqint2 : seq<int> := [102, 0];
var seqint3 : seq<int> := [101, 0];
var seqint4 : seq<int> := [100, 0];
var seqint5 : seq<int> := [99, 0];
var seqint6 : seq<int> := [98, 0];
var seqint7 : seq<int> := [97, 0];
var seqint8 : seq<int> := [96, 0];
var seqint9 : seq<int> := [95, 0];
var seqint10 : seq<int> := [94, 0];
var seqint11 : seq<int> := [93, 0];
var seqint12 : seq<int> := [92, 0, 0];
var seqint13 : seq<int> := [91, 0];
var seqint14 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 12.9830307 s

method {:test} Test13() {
var seqint0 : seq<int> := [143, 0, 0, 0];
var seqint1 : seq<int> := [142, 0, 0, 0];
var seqint2 : seq<int> := [140, 0, 0];
var seqint3 : seq<int> := [139, 0, 0];
var seqint4 : seq<int> := [138, 0, 0];
var seqint5 : seq<int> := [137, 0, 0];
var seqint6 : seq<int> := [136, 0, 0];
var seqint7 : seq<int> := [135, 0, 0];
var seqint8 : seq<int> := [134, 0, 0];
var seqint9 : seq<int> := [133, 0, 0];
var seqint10 : seq<int> := [132, 0, 0];
var seqint11 : seq<int> := [145, 0, 0];
var seqint12 : seq<int> := [144, 0, 0, 0];
var seqint13 : seq<int> := [146, 0, 0];
var seqint14 : seq<int> := [147];
var seqint15 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 5 - TIME: 14.2307767 s

method {:test} Test14() {
var seqint0 : seq<int> := [55, 0, 0, 0, 0];
var seqint1 : seq<int> := [54, 0, 0, 0, 0];
var seqint2 : seq<int> := [52, 0, 0, 0];
var seqint3 : seq<int> := [51, 0, 0, 0];
var seqint4 : seq<int> := [50, 0, 0, 0];
var seqint5 : seq<int> := [49, 0, 0, 0];
var seqint6 : seq<int> := [48, 0, 0, 0];
var seqint7 : seq<int> := [47, 0, 0, 0];
var seqint8 : seq<int> := [46, 0, 0, 0];
var seqint9 : seq<int> := [58, 0, 0, 0];
var seqint10 : seq<int> := [57, 0, 0, 0];
var seqint11 : seq<int> := [56, 0, 0, 0];
var seqint12 : seq<int> := [45, 0, 0, 0, 0];
var seqint13 : seq<int> := [44, 0, 0, 0];
var seqint14 : seq<int> := [42, 0];
var seqint15 : seq<int> := [37];
var seqint16 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 15.5159499 s

method {:test} Test15() {
var seqint0 : seq<int> := [282, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [281, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [279, 0, 0, 0, 0];
var seqint3 : seq<int> := [278, 0, 0, 0, 0];
var seqint4 : seq<int> := [277, 0, 0, 0, 0];
var seqint5 : seq<int> := [276, 0, 0, 0, 0];
var seqint6 : seq<int> := [275, 0, 0, 0, 0];
var seqint7 : seq<int> := [274, 0, 0, 0, 0];
var seqint8 : seq<int> := [273, 0, 0, 0, 0];
var seqint9 : seq<int> := [288, 0, 0, 0, 0];
var seqint10 : seq<int> := [287, 0, 0, 0, 0];
var seqint11 : seq<int> := [286, 0, 0, 0, 0];
var seqint12 : seq<int> := [285, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [284, 0, 0, 0, 0];
var seqint14 : seq<int> := [283, 0, 0];
var seqint15 : seq<int> := [290, 0];
var seqint16 : seq<int> := [289];
var seqint17 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 17.2199177 s

method {:test} Test16() {
var seqint0 : seq<int> := [379, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [378, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [376, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [375, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [374, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [373, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [372, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [371, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [370, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [385, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [384, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [383, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [382, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [381, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [380, 0, 0, 0];
var seqint15 : seq<int> := [387, 0, 0];
var seqint16 : seq<int> := [386, 0];
var seqint17 : seq<int> := [388];
var seqint18 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 18.9982686 s

method {:test} Test17() {
var seqint0 : seq<int> := [495, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [494, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [492, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [491, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [490, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [489, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [488, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [487, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [486, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [504, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [503, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [502, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [501, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [500, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [499, 0, 0, 0, 0];
var seqint15 : seq<int> := [498, 0, 0, 0];
var seqint16 : seq<int> := [497, 0, 0];
var seqint17 : seq<int> := [496, 0];
var seqint18 : seq<int> := [505];
var seqint19 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 21.024066 s

method {:test} Test18() {
var seqint0 : seq<int> := [631, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [630, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [628, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [627, 0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [626, 0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [625, 0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [624, 0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [623, 0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [622, 0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [640, 0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [639, 0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [638, 0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [637, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [636, 0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [635, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [634, 0, 0, 0, 0];
var seqint16 : seq<int> := [633, 0, 0, 0];
var seqint17 : seq<int> := [632, 0, 0];
var seqint18 : seq<int> := [641, 0];
var seqint19 : seq<int> := [642];
var seqint20 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 23.0268595 s
