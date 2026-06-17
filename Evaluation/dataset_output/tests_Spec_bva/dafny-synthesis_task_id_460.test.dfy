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

// REPEAT 1 - TIME: 7.1943395 s

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

// REPEAT 2 - TIME: 8.0807221 s

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

// REPEAT 3 - TIME: 9.1596803 s

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

// REPEAT 4 - TIME: 10.6188553 s

method {:test} Test13() {
var seqint0 : seq<int> := [376, 0, 0, 0];
var seqint1 : seq<int> := [375, 0, 0, 0];
var seqint2 : seq<int> := [374, 0, 0];
var seqint3 : seq<int> := [373, 0, 0];
var seqint4 : seq<int> := [371, 0, 0];
var seqint5 : seq<int> := [370, 0, 0];
var seqint6 : seq<int> := [369, 0, 0];
var seqint7 : seq<int> := [368, 0, 0];
var seqint8 : seq<int> := [367, 0, 0];
var seqint9 : seq<int> := [366, 0, 0];
var seqint10 : seq<int> := [365, 0, 0];
var seqint11 : seq<int> := [364, 0, 0];
var seqint12 : seq<int> := [363, 0, 0];
var seqint13 : seq<int> := [362, 0, 0];
var seqint14 : seq<int> := [361, 0, 0];
var seqint15 : seq<int> := [360, 0, 0];
var seqint16 : seq<int> := [359, 0, 0];
var seqint17 : seq<int> := [358, 0, 0];
var seqint18 : seq<int> := [357, 0, 0];
var seqint19 : seq<int> := [356, 0, 0];
var seqint20 : seq<int> := [355, 0, 0];
var seqint21 : seq<int> := [354, 0, 0];
var seqint22 : seq<int> := [353, 0, 0];
var seqint23 : seq<int> := [352, 0, 0];
var seqint24 : seq<int> := [351, 0, 0];
var seqint25 : seq<int> := [350, 0, 0];
var seqint26 : seq<int> := [349, 0, 0];
var seqint27 : seq<int> := [348, 0, 0];
var seqint28 : seq<int> := [347, 0, 0];
var seqint29 : seq<int> := [346, 0, 0];
var seqint30 : seq<int> := [345, 0, 0];
var seqint31 : seq<int> := [344, 0, 0];
var seqint32 : seq<int> := [343, 0, 0];
var seqint33 : seq<int> := [385, 0, 0];
var seqint34 : seq<int> := [384, 0, 0];
var seqint35 : seq<int> := [383, 0, 0];
var seqint36 : seq<int> := [382, 0, 0];
var seqint37 : seq<int> := [381, 0, 0];
var seqint38 : seq<int> := [380, 0, 0];
var seqint39 : seq<int> := [379, 0, 0];
var seqint40 : seq<int> := [378, 0, 0, 0];
var seqint41 : seq<int> := [377, 0];
var seqint42 : seq<int> := [386];
var seqint43 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 5 - TIME: 12.2939417 s

method {:test} Test14() {
var seqint0 : seq<int> := [550, 0, 0, 0, 0];
var seqint1 : seq<int> := [549, 0, 0, 0, 0];
var seqint2 : seq<int> := [548, 0, 0, 0];
var seqint3 : seq<int> := [547, 0, 0, 0];
var seqint4 : seq<int> := [546, 0, 0, 0];
var seqint5 : seq<int> := [545, 0, 0, 0];
var seqint6 : seq<int> := [543, 0, 0, 0];
var seqint7 : seq<int> := [542, 0, 0, 0];
var seqint8 : seq<int> := [541, 0, 0, 0];
var seqint9 : seq<int> := [540, 0, 0, 0];
var seqint10 : seq<int> := [539, 0, 0, 0];
var seqint11 : seq<int> := [538, 0, 0, 0];
var seqint12 : seq<int> := [537, 0, 0, 0];
var seqint13 : seq<int> := [536, 0, 0, 0];
var seqint14 : seq<int> := [535, 0, 0, 0];
var seqint15 : seq<int> := [534, 0, 0, 0];
var seqint16 : seq<int> := [533, 0, 0, 0];
var seqint17 : seq<int> := [532, 0, 0, 0];
var seqint18 : seq<int> := [531, 0, 0, 0];
var seqint19 : seq<int> := [530, 0, 0, 0];
var seqint20 : seq<int> := [529, 0, 0, 0];
var seqint21 : seq<int> := [528, 0, 0, 0];
var seqint22 : seq<int> := [527, 0, 0, 0];
var seqint23 : seq<int> := [526, 0, 0, 0];
var seqint24 : seq<int> := [525, 0, 0, 0];
var seqint25 : seq<int> := [524, 0, 0, 0];
var seqint26 : seq<int> := [523, 0, 0, 0];
var seqint27 : seq<int> := [522, 0, 0, 0];
var seqint28 : seq<int> := [521, 0, 0, 0];
var seqint29 : seq<int> := [520, 0, 0, 0];
var seqint30 : seq<int> := [519, 0, 0, 0];
var seqint31 : seq<int> := [518, 0, 0, 0];
var seqint32 : seq<int> := [517, 0, 0, 0];
var seqint33 : seq<int> := [559, 0, 0, 0];
var seqint34 : seq<int> := [558, 0, 0, 0];
var seqint35 : seq<int> := [557, 0, 0, 0];
var seqint36 : seq<int> := [556, 0, 0, 0];
var seqint37 : seq<int> := [555, 0, 0, 0];
var seqint38 : seq<int> := [554, 0, 0, 0];
var seqint39 : seq<int> := [553, 0, 0, 0];
var seqint40 : seq<int> := [552, 0, 0, 0, 0];
var seqint41 : seq<int> := [551, 0, 0];
var seqint42 : seq<int> := [560, 0];
var seqint43 : seq<int> := [561];
var seqint44 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 6 - TIME: 14.5017878 s

method {:test} Test15() {
var seqint0 : seq<int> := [769, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [768, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [767, 0, 0, 0, 0];
var seqint3 : seq<int> := [766, 0, 0, 0, 0];
var seqint4 : seq<int> := [765, 0, 0, 0, 0];
var seqint5 : seq<int> := [764, 0, 0, 0, 0];
var seqint6 : seq<int> := [763, 0, 0, 0, 0];
var seqint7 : seq<int> := [762, 0, 0, 0, 0];
var seqint8 : seq<int> := [761, 0, 0, 0, 0];
var seqint9 : seq<int> := [759, 0, 0, 0, 0];
var seqint10 : seq<int> := [758, 0, 0, 0, 0];
var seqint11 : seq<int> := [757, 0, 0, 0, 0];
var seqint12 : seq<int> := [756, 0, 0, 0, 0];
var seqint13 : seq<int> := [755, 0, 0, 0, 0];
var seqint14 : seq<int> := [754, 0, 0, 0, 0];
var seqint15 : seq<int> := [753, 0, 0, 0, 0];
var seqint16 : seq<int> := [752, 0, 0, 0, 0];
var seqint17 : seq<int> := [751, 0, 0, 0, 0];
var seqint18 : seq<int> := [750, 0, 0, 0, 0];
var seqint19 : seq<int> := [749, 0, 0, 0, 0];
var seqint20 : seq<int> := [748, 0, 0, 0, 0];
var seqint21 : seq<int> := [747, 0, 0, 0, 0];
var seqint22 : seq<int> := [746, 0, 0, 0, 0];
var seqint23 : seq<int> := [745, 0, 0, 0, 0];
var seqint24 : seq<int> := [744, 0, 0, 0, 0];
var seqint25 : seq<int> := [743, 0, 0, 0, 0];
var seqint26 : seq<int> := [742, 0, 0, 0, 0];
var seqint27 : seq<int> := [741, 0, 0, 0, 0];
var seqint28 : seq<int> := [740, 0, 0, 0, 0];
var seqint29 : seq<int> := [739, 0, 0, 0, 0];
var seqint30 : seq<int> := [738, 0, 0, 0, 0];
var seqint31 : seq<int> := [737, 0, 0, 0, 0];
var seqint32 : seq<int> := [736, 0, 0, 0, 0];
var seqint33 : seq<int> := [778, 0, 0, 0, 0];
var seqint34 : seq<int> := [777, 0, 0, 0, 0];
var seqint35 : seq<int> := [776, 0, 0, 0, 0];
var seqint36 : seq<int> := [775, 0, 0, 0, 0];
var seqint37 : seq<int> := [774, 0, 0, 0, 0];
var seqint38 : seq<int> := [773, 0, 0, 0, 0];
var seqint39 : seq<int> := [772, 0, 0, 0, 0];
var seqint40 : seq<int> := [771, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [770, 0, 0, 0];
var seqint42 : seq<int> := [780, 0, 0];
var seqint43 : seq<int> := [779, 0];
var seqint44 : seq<int> := [781];
var seqint45 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 7 - TIME: 16.6020046 s

method {:test} Test16() {
var seqint0 : seq<int> := [1021, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [1020, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [1018, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [1017, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [1016, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [1015, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [1014, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [1013, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [1012, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [1011, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [1009, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [1008, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [1007, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [1006, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [1005, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [1004, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [1003, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [1002, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [1001, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [1047, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [1046, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [1045, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [1044, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [1043, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [1042, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [1041, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [1040, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [1039, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [1038, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [1037, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [1036, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [1035, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [1034, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [1033, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [1032, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [1031, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [1030, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [1029, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [1028, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [1027, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [1026, 0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [1025, 0, 0, 0, 0];
var seqint42 : seq<int> := [1024, 0, 0, 0];
var seqint43 : seq<int> := [1023, 0, 0];
var seqint44 : seq<int> := [1022, 0];
var seqint45 : seq<int> := [1048];
var seqint46 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 8 - TIME: 19.1251186 s

method {:test} Test17() {
var seqint0 : seq<int> := [1332, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [1331, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [1330, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [1329, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [1328, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [1327, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [1326, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [1325, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [1324, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [1323, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [1322, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [1321, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [1320, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [1318, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [1317, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [1316, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [1315, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [1314, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [1313, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [1358, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [1357, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [1356, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [1355, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [1354, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [1353, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [1352, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [1351, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [1350, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [1349, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [1348, 0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [1347, 0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [1346, 0, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [1345, 0, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [1344, 0, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [1343, 0, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [1342, 0, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [1341, 0, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [1340, 0, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [1339, 0, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [1338, 0, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [1337, 0, 0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [1336, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [1335, 0, 0, 0, 0];
var seqint43 : seq<int> := [1334, 0, 0, 0];
var seqint44 : seq<int> := [1333, 0, 0];
var seqint45 : seq<int> := [1359, 0];
var seqint46 : seq<int> := [1360];
var seqint47 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 9 - TIME: 22.2796634 s

method {:test} Test18() {
var seqint0 : seq<int> := [1692, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [1691, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [1690, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [1689, 0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [1688, 0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [1687, 0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [1686, 0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [1685, 0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [1684, 0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [1683, 0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [1682, 0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [1681, 0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [1680, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [1679, 0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [1677, 0, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [1676, 0, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [1675, 0, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [1674, 0, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [1673, 0, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [1718, 0, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [1717, 0, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [1716, 0, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [1715, 0, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [1714, 0, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [1713, 0, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [1712, 0, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [1711, 0, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [1710, 0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [1709, 0, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [1708, 0, 0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [1707, 0, 0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [1706, 0, 0, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [1705, 0, 0, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [1704, 0, 0, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [1703, 0, 0, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [1702, 0, 0, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [1701, 0, 0, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [1700, 0, 0, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [1699, 0, 0, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [1698, 0, 0, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [1697, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [1696, 0, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [1695, 0, 0, 0, 0, 0];
var seqint43 : seq<int> := [1694, 0, 0, 0, 0];
var seqint44 : seq<int> := [1693, 0, 0, 0];
var seqint45 : seq<int> := [1719, 0, 0];
var seqint46 : seq<int> := [1720, 0];
var seqint47 : seq<int> := [1721];
var seqint48 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48];
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GetFirstElements(seqseqint0);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqseqint0[i][0];
}

// REPEAT 10 - TIME: 26.5101359 s
