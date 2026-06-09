
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

// REPEAT 6 - TIME: 12.8438802 s