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

// REPEAT 1 - TIME: 2.8792275 s

method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [27];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 2 - TIME: 4.1603777 s

method {:test} Test2() {
var seqint0 : seq<int> := [];
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
var seqint25 : seq<int> := [];
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
var seqint39 : seq<int> := [];
var seqint40 : seq<int> := [31];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 3 - TIME: 5.2312779 s

method {:test} Test3() {
var seqint0 : seq<int> := [79];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 4 - TIME: 6.3059227 s

method {:test} Test4() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [82];
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
var seqint25 : seq<int> := [];
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
var seqint39 : seq<int> := [];
var seqint40 : seq<int> := [];
var seqint41 : seq<int> := [85];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 5 - TIME: 7.2924712 s

method {:test} Test5() {
var seqint0 : seq<int> := [130];
var seqint1 : seq<int> := [127];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 8.428359 s

method {:test} Test6() {
var seqint0 : seq<int> := [138];
var seqint1 : seq<int> := [136];
var seqint2 : seq<int> := [139];
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
var seqint14 : seq<int> := [141];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 9.4589896 s

method {:test} Test7() {
var seqint0 : seq<int> := [168];
var seqint1 : seq<int> := [158];
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
var seqint12 : seq<int> := [161];
var seqint13 : seq<int> := [163];
var seqint14 : seq<int> := [];
var seqint15 : seq<int> := [165];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 10.236043 s

method {:test} Test8() {
var seqint0 : seq<int> := [187];
var seqint1 : seq<int> := [185];
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
var seqint14 : seq<int> := [188];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 11.1468047 s

method {:test} Test9() {
var seqint0 : seq<int> := [219];
var seqint1 : seq<int> := [211];
var seqint2 : seq<int> := [206];
var seqint3 : seq<int> := [205];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 12.2543912 s
