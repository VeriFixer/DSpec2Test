
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

// REPEAT 8 - TIME: 17.1356554 s