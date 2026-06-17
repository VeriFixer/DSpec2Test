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

// REPEAT 1 - TIME: 10.4790997 s

method {:test} Test1() {
var seqint0 : seq<int> := [25];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 2 - TIME: 17.0204565 s

method {:test} Test2() {
var seqint0 : seq<int> := [31, 0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 23.827407 s

method {:test} Test3() {
var seqint0 : seq<int> := [27, 0, 0];
var seqint1 : seq<int> := [26];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 31.7613322 s

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

// REPEAT 5 - TIME: 39.5449331 s

method {:test} Test5() {
var seqint0 : seq<int> := [29, 0, 0, 0, 0];
var seqint1 : seq<int> := [30, 0, 0];
var seqint2 : seq<int> := [28];
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
var seqint17 : seq<int> := [63];
var seqint18 : seq<int> := [64];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 47.5103918 s

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
var seqint17 : seq<int> := [53, 0];
var seqint18 : seq<int> := [33, 0];
var seqint19 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 57.0717548 s

method {:test} Test7() {
var seqint0 : seq<int> := [72, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [71, 0, 0, 0, 0];
var seqint2 : seq<int> := [70, 0, 0];
var seqint3 : seq<int> := [69, 0];
var seqint4 : seq<int> := [68, 0];
var seqint5 : seq<int> := [67, 0];
var seqint6 : seq<int> := [66, 0];
var seqint7 : seq<int> := [65, 0];
var seqint8 : seq<int> := [62, 0];
var seqint9 : seq<int> := [61, 0];
var seqint10 : seq<int> := [60, 0];
var seqint11 : seq<int> := [59, 0];
var seqint12 : seq<int> := [58, 0];
var seqint13 : seq<int> := [57, 0];
var seqint14 : seq<int> := [56, 0];
var seqint15 : seq<int> := [55, 0];
var seqint16 : seq<int> := [54, 0];
var seqint17 : seq<int> := [74, 0, 0];
var seqint18 : seq<int> := [73, 0, 0];
var seqint19 : seq<int> := [75];
var seqint20 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 67.8915477 s

method {:test} Test8() {
var seqint0 : seq<int> := [213, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [232, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [231, 0, 0, 0];
var seqint3 : seq<int> := [230, 0, 0];
var seqint4 : seq<int> := [229, 0, 0];
var seqint5 : seq<int> := [228, 0, 0];
var seqint6 : seq<int> := [227, 0, 0];
var seqint7 : seq<int> := [226, 0, 0];
var seqint8 : seq<int> := [225, 0, 0];
var seqint9 : seq<int> := [224, 0, 0];
var seqint10 : seq<int> := [223, 0, 0];
var seqint11 : seq<int> := [222, 0, 0];
var seqint12 : seq<int> := [221, 0, 0];
var seqint13 : seq<int> := [220, 0, 0];
var seqint14 : seq<int> := [219, 0, 0];
var seqint15 : seq<int> := [218, 0, 0];
var seqint16 : seq<int> := [217, 0, 0];
var seqint17 : seq<int> := [216, 0, 0, 0];
var seqint18 : seq<int> := [215, 0, 0, 0];
var seqint19 : seq<int> := [214, 0];
var seqint20 : seq<int> := [233];
var seqint21 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 82.3605786 s

method {:test} Test9() {
var seqint0 : seq<int> := [306, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [325, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [324, 0, 0, 0, 0];
var seqint3 : seq<int> := [323, 0, 0, 0];
var seqint4 : seq<int> := [322, 0, 0, 0];
var seqint5 : seq<int> := [321, 0, 0, 0];
var seqint6 : seq<int> := [320, 0, 0, 0];
var seqint7 : seq<int> := [319, 0, 0, 0];
var seqint8 : seq<int> := [318, 0, 0, 0];
var seqint9 : seq<int> := [317, 0, 0, 0];
var seqint10 : seq<int> := [316, 0, 0, 0];
var seqint11 : seq<int> := [315, 0, 0, 0];
var seqint12 : seq<int> := [314, 0, 0, 0];
var seqint13 : seq<int> := [313, 0, 0, 0];
var seqint14 : seq<int> := [312, 0, 0, 0];
var seqint15 : seq<int> := [311, 0, 0, 0];
var seqint16 : seq<int> := [310, 0, 0, 0];
var seqint17 : seq<int> := [309, 0, 0, 0, 0];
var seqint18 : seq<int> := [308, 0, 0, 0, 0];
var seqint19 : seq<int> := [307, 0, 0];
var seqint20 : seq<int> := [326, 0];
var seqint21 : seq<int> := [327];
var seqint22 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 100.3083779 s
