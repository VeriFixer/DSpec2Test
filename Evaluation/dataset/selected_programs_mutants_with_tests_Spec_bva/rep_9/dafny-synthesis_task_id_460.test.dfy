
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

// REPEAT 9 - TIME: 19.9463065 s