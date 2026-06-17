// dafny-synthesis_task_id_401.dfy

method {:testEntry} IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| > 0 && |b| > 0
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
  ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
  {
    var subResult := [];
    for j := 0 to |a[i]|
      invariant 0 <= j <= |a[i]|
      invariant |subResult| == j
      invariant forall k :: 0 <= k < j ==> subResult[k] == a[i][k] + b[i][k]
    {
    }
    result := result + [subResult];
  }
}


method {:testEntry} IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{
    result := [];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
    {
        var subResult := [];
        for j := 0 to |a[i]|
            invariant 0 <= j <= |a[i]|
            invariant |subResult| == j
            invariant forall k :: 0 <= k < j ==> subResult[k] == a[i][k] + b[i][k]
        {
            subResult := subResult + [a[i][j] + b[i][j]];
        }
        result := result + [subResult];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
var seqint1 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint1];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 1 - TIME: 2.8114272 s

method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
var seqint2 : seq<int> := [0];
var seqint3 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint2, seqint3];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 2 - TIME: 3.8541343 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0];
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
var seqint40 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40];
var seqint41 : seq<int> := [0, 0];
var seqint42 : seq<int> := [0];
var seqint43 : seq<int> := [];
var seqint44 : seq<int> := [];
var seqint45 : seq<int> := [];
var seqint46 : seq<int> := [];
var seqint47 : seq<int> := [];
var seqint48 : seq<int> := [];
var seqint49 : seq<int> := [];
var seqint50 : seq<int> := [];
var seqint51 : seq<int> := [];
var seqint52 : seq<int> := [];
var seqint53 : seq<int> := [];
var seqint54 : seq<int> := [];
var seqint55 : seq<int> := [];
var seqint56 : seq<int> := [];
var seqint57 : seq<int> := [];
var seqint58 : seq<int> := [];
var seqint59 : seq<int> := [];
var seqint60 : seq<int> := [];
var seqint61 : seq<int> := [];
var seqint62 : seq<int> := [];
var seqint63 : seq<int> := [];
var seqint64 : seq<int> := [];
var seqint65 : seq<int> := [];
var seqint66 : seq<int> := [];
var seqint67 : seq<int> := [];
var seqint68 : seq<int> := [];
var seqint69 : seq<int> := [];
var seqint70 : seq<int> := [];
var seqint71 : seq<int> := [];
var seqint72 : seq<int> := [];
var seqint73 : seq<int> := [];
var seqint74 : seq<int> := [];
var seqint75 : seq<int> := [];
var seqint76 : seq<int> := [];
var seqint77 : seq<int> := [];
var seqint78 : seq<int> := [];
var seqint79 : seq<int> := [];
var seqint80 : seq<int> := [];
var seqint81 : seq<int> := [0];
var seqseqint1 : seq<seq<int>> := [seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 3 - TIME: 4.9347774 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [0, 0];
var seqint2 : seq<int> := [0];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [0];
var seqint7 : seq<int> := [0];
var seqint8 : seq<int> := [0];
var seqint9 : seq<int> := [0];
var seqint10 : seq<int> := [0];
var seqint11 : seq<int> := [0];
var seqint12 : seq<int> := [0];
var seqint13 : seq<int> := [0];
var seqint14 : seq<int> := [0];
var seqint15 : seq<int> := [0];
var seqint16 : seq<int> := [0];
var seqint17 : seq<int> := [0];
var seqint18 : seq<int> := [0];
var seqint19 : seq<int> := [0];
var seqint20 : seq<int> := [0];
var seqint21 : seq<int> := [0];
var seqint22 : seq<int> := [0];
var seqint23 : seq<int> := [0];
var seqint24 : seq<int> := [0];
var seqint25 : seq<int> := [0];
var seqint26 : seq<int> := [0];
var seqint27 : seq<int> := [0];
var seqint28 : seq<int> := [0];
var seqint29 : seq<int> := [0];
var seqint30 : seq<int> := [0];
var seqint31 : seq<int> := [0];
var seqint32 : seq<int> := [0];
var seqint33 : seq<int> := [0];
var seqint34 : seq<int> := [0];
var seqint35 : seq<int> := [0];
var seqint36 : seq<int> := [0];
var seqint37 : seq<int> := [0];
var seqint38 : seq<int> := [0];
var seqint39 : seq<int> := [0];
var seqint40 : seq<int> := [];
var seqint41 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41];
var seqint42 : seq<int> := [0, 0, 0];
var seqint43 : seq<int> := [0, 0];
var seqint44 : seq<int> := [0];
var seqint45 : seq<int> := [0];
var seqint46 : seq<int> := [0];
var seqint47 : seq<int> := [0];
var seqint48 : seq<int> := [0];
var seqint49 : seq<int> := [0];
var seqint50 : seq<int> := [0];
var seqint51 : seq<int> := [0];
var seqint52 : seq<int> := [0];
var seqint53 : seq<int> := [0];
var seqint54 : seq<int> := [0];
var seqint55 : seq<int> := [0];
var seqint56 : seq<int> := [0];
var seqint57 : seq<int> := [0];
var seqint58 : seq<int> := [0];
var seqint59 : seq<int> := [0];
var seqint60 : seq<int> := [0];
var seqint61 : seq<int> := [0];
var seqint62 : seq<int> := [0];
var seqint63 : seq<int> := [0];
var seqint64 : seq<int> := [0];
var seqint65 : seq<int> := [0];
var seqint66 : seq<int> := [0];
var seqint67 : seq<int> := [0];
var seqint68 : seq<int> := [0];
var seqint69 : seq<int> := [0];
var seqint70 : seq<int> := [0];
var seqint71 : seq<int> := [0];
var seqint72 : seq<int> := [0];
var seqint73 : seq<int> := [0];
var seqint74 : seq<int> := [0];
var seqint75 : seq<int> := [0];
var seqint76 : seq<int> := [0];
var seqint77 : seq<int> := [0];
var seqint78 : seq<int> := [0];
var seqint79 : seq<int> := [0];
var seqint80 : seq<int> := [0];
var seqint81 : seq<int> := [0];
var seqint82 : seq<int> := [];
var seqint83 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 4 - TIME: 6.8721934 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0];
var seqint2 : seq<int> := [0, 0];
var seqint3 : seq<int> := [0, 0];
var seqint4 : seq<int> := [0, 0];
var seqint5 : seq<int> := [0, 0];
var seqint6 : seq<int> := [0, 0];
var seqint7 : seq<int> := [0, 0];
var seqint8 : seq<int> := [0, 0];
var seqint9 : seq<int> := [0, 0];
var seqint10 : seq<int> := [0, 0];
var seqint11 : seq<int> := [0, 0];
var seqint12 : seq<int> := [0, 0];
var seqint13 : seq<int> := [0, 0];
var seqint14 : seq<int> := [0, 0];
var seqint15 : seq<int> := [0, 0];
var seqint16 : seq<int> := [0, 0];
var seqint17 : seq<int> := [0, 0];
var seqint18 : seq<int> := [0, 0];
var seqint19 : seq<int> := [0, 0];
var seqint20 : seq<int> := [0, 0];
var seqint21 : seq<int> := [0, 0];
var seqint22 : seq<int> := [0, 0];
var seqint23 : seq<int> := [0, 0];
var seqint24 : seq<int> := [0, 0];
var seqint25 : seq<int> := [0, 0];
var seqint26 : seq<int> := [0, 0];
var seqint27 : seq<int> := [0, 0];
var seqint28 : seq<int> := [0, 0];
var seqint29 : seq<int> := [0, 0];
var seqint30 : seq<int> := [0, 0];
var seqint31 : seq<int> := [0, 0];
var seqint32 : seq<int> := [0, 0];
var seqint33 : seq<int> := [0, 0];
var seqint34 : seq<int> := [0, 0];
var seqint35 : seq<int> := [0, 0];
var seqint36 : seq<int> := [0, 0];
var seqint37 : seq<int> := [0, 0];
var seqint38 : seq<int> := [0, 0];
var seqint39 : seq<int> := [0, 0];
var seqint40 : seq<int> := [0, 0];
var seqint41 : seq<int> := [0];
var seqint42 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42];
var seqint43 : seq<int> := [0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0];
var seqint45 : seq<int> := [0, 0];
var seqint46 : seq<int> := [0, 0];
var seqint47 : seq<int> := [0, 0];
var seqint48 : seq<int> := [0, 0];
var seqint49 : seq<int> := [0, 0];
var seqint50 : seq<int> := [0, 0];
var seqint51 : seq<int> := [0, 0];
var seqint52 : seq<int> := [0, 0];
var seqint53 : seq<int> := [0, 0];
var seqint54 : seq<int> := [0, 0];
var seqint55 : seq<int> := [0, 0];
var seqint56 : seq<int> := [0, 0];
var seqint57 : seq<int> := [0, 0];
var seqint58 : seq<int> := [0, 0];
var seqint59 : seq<int> := [0, 0];
var seqint60 : seq<int> := [0, 0];
var seqint61 : seq<int> := [0, 0];
var seqint62 : seq<int> := [0, 0];
var seqint63 : seq<int> := [0, 0];
var seqint64 : seq<int> := [0, 0];
var seqint65 : seq<int> := [0, 0];
var seqint66 : seq<int> := [0, 0];
var seqint67 : seq<int> := [0, 0];
var seqint68 : seq<int> := [0, 0];
var seqint69 : seq<int> := [0, 0];
var seqint70 : seq<int> := [0, 0];
var seqint71 : seq<int> := [0, 0];
var seqint72 : seq<int> := [0, 0];
var seqint73 : seq<int> := [0, 0];
var seqint74 : seq<int> := [0, 0];
var seqint75 : seq<int> := [0, 0];
var seqint76 : seq<int> := [0, 0];
var seqint77 : seq<int> := [0, 0];
var seqint78 : seq<int> := [0, 0];
var seqint79 : seq<int> := [0, 0];
var seqint80 : seq<int> := [0, 0];
var seqint81 : seq<int> := [0, 0];
var seqint82 : seq<int> := [0, 0];
var seqint83 : seq<int> := [0, 0];
var seqint84 : seq<int> := [0];
var seqint85 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83, seqint84, seqint85];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 5 - TIME: 9.2375756 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0];
var seqint41 : seq<int> := [0, 0];
var seqint42 : seq<int> := [0];
var seqint43 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43];
var seqint44 : seq<int> := [0, 0, 0, 0, 0];
var seqint45 : seq<int> := [0, 0, 0, 0];
var seqint46 : seq<int> := [0, 0, 0];
var seqint47 : seq<int> := [0, 0, 0];
var seqint48 : seq<int> := [0, 0, 0];
var seqint49 : seq<int> := [0, 0, 0];
var seqint50 : seq<int> := [0, 0, 0];
var seqint51 : seq<int> := [0, 0, 0];
var seqint52 : seq<int> := [0, 0, 0];
var seqint53 : seq<int> := [0, 0, 0];
var seqint54 : seq<int> := [0, 0, 0];
var seqint55 : seq<int> := [0, 0, 0];
var seqint56 : seq<int> := [0, 0, 0];
var seqint57 : seq<int> := [0, 0, 0];
var seqint58 : seq<int> := [0, 0, 0];
var seqint59 : seq<int> := [0, 0, 0];
var seqint60 : seq<int> := [0, 0, 0];
var seqint61 : seq<int> := [0, 0, 0];
var seqint62 : seq<int> := [0, 0, 0];
var seqint63 : seq<int> := [0, 0, 0];
var seqint64 : seq<int> := [0, 0, 0];
var seqint65 : seq<int> := [0, 0, 0];
var seqint66 : seq<int> := [0, 0, 0];
var seqint67 : seq<int> := [0, 0, 0];
var seqint68 : seq<int> := [0, 0, 0];
var seqint69 : seq<int> := [0, 0, 0];
var seqint70 : seq<int> := [0, 0, 0];
var seqint71 : seq<int> := [0, 0, 0];
var seqint72 : seq<int> := [0, 0, 0];
var seqint73 : seq<int> := [0, 0, 0];
var seqint74 : seq<int> := [0, 0, 0];
var seqint75 : seq<int> := [0, 0, 0];
var seqint76 : seq<int> := [0, 0, 0];
var seqint77 : seq<int> := [0, 0, 0];
var seqint78 : seq<int> := [0, 0, 0];
var seqint79 : seq<int> := [0, 0, 0];
var seqint80 : seq<int> := [0, 0, 0];
var seqint81 : seq<int> := [0, 0, 0];
var seqint82 : seq<int> := [0, 0, 0];
var seqint83 : seq<int> := [0, 0, 0];
var seqint84 : seq<int> := [0, 0, 0];
var seqint85 : seq<int> := [0, 0];
var seqint86 : seq<int> := [0];
var seqint87 : seq<int> := [0];
var seqseqint1 : seq<seq<int>> := [seqint44, seqint45, seqint46, seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83, seqint84, seqint85, seqint86, seqint87];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 6 - TIME: 11.5516635 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0, 0];
var seqint41 : seq<int> := [0, 0, 0];
var seqint42 : seq<int> := [0, 0];
var seqint43 : seq<int> := [0, 0];
var seqint44 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44];
var seqint45 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint46 : seq<int> := [0, 0, 0, 0, 0];
var seqint47 : seq<int> := [0, 0, 0, 0];
var seqint48 : seq<int> := [0, 0, 0, 0];
var seqint49 : seq<int> := [0, 0, 0, 0];
var seqint50 : seq<int> := [0, 0, 0, 0];
var seqint51 : seq<int> := [0, 0, 0, 0];
var seqint52 : seq<int> := [0, 0, 0, 0];
var seqint53 : seq<int> := [0, 0, 0, 0];
var seqint54 : seq<int> := [0, 0, 0, 0];
var seqint55 : seq<int> := [0, 0, 0, 0];
var seqint56 : seq<int> := [0, 0, 0, 0];
var seqint57 : seq<int> := [0, 0, 0, 0];
var seqint58 : seq<int> := [0, 0, 0, 0];
var seqint59 : seq<int> := [0, 0, 0, 0];
var seqint60 : seq<int> := [0, 0, 0, 0];
var seqint61 : seq<int> := [0, 0, 0, 0];
var seqint62 : seq<int> := [0, 0, 0, 0];
var seqint63 : seq<int> := [0, 0, 0, 0];
var seqint64 : seq<int> := [0, 0, 0, 0];
var seqint65 : seq<int> := [0, 0, 0, 0];
var seqint66 : seq<int> := [0, 0, 0, 0];
var seqint67 : seq<int> := [0, 0, 0, 0];
var seqint68 : seq<int> := [0, 0, 0, 0];
var seqint69 : seq<int> := [0, 0, 0, 0];
var seqint70 : seq<int> := [0, 0, 0, 0];
var seqint71 : seq<int> := [0, 0, 0, 0];
var seqint72 : seq<int> := [0, 0, 0, 0];
var seqint73 : seq<int> := [0, 0, 0, 0];
var seqint74 : seq<int> := [0, 0, 0, 0];
var seqint75 : seq<int> := [0, 0, 0, 0];
var seqint76 : seq<int> := [0, 0, 0, 0];
var seqint77 : seq<int> := [0, 0, 0, 0];
var seqint78 : seq<int> := [0, 0, 0, 0];
var seqint79 : seq<int> := [0, 0, 0, 0];
var seqint80 : seq<int> := [0, 0, 0, 0];
var seqint81 : seq<int> := [0, 0, 0, 0];
var seqint82 : seq<int> := [0, 0, 0, 0];
var seqint83 : seq<int> := [0, 0, 0, 0];
var seqint84 : seq<int> := [0, 0, 0, 0];
var seqint85 : seq<int> := [0, 0, 0, 0];
var seqint86 : seq<int> := [0, 0, 0];
var seqint87 : seq<int> := [0, 0];
var seqint88 : seq<int> := [0, 0];
var seqint89 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint45, seqint46, seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83, seqint84, seqint85, seqint86, seqint87, seqint88, seqint89];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 7 - TIME: 14.2195104 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0, 0, 0];
var seqint41 : seq<int> := [0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0];
var seqint43 : seq<int> := [];
var seqint44 : seq<int> := [0];
var seqint45 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45];
var seqint46 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint47 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint48 : seq<int> := [0, 0, 0, 0, 0];
var seqint49 : seq<int> := [0, 0, 0, 0, 0];
var seqint50 : seq<int> := [0, 0, 0, 0, 0];
var seqint51 : seq<int> := [0, 0, 0, 0, 0];
var seqint52 : seq<int> := [0, 0, 0, 0, 0];
var seqint53 : seq<int> := [0, 0, 0, 0, 0];
var seqint54 : seq<int> := [0, 0, 0, 0, 0];
var seqint55 : seq<int> := [0, 0, 0, 0, 0];
var seqint56 : seq<int> := [0, 0, 0, 0, 0];
var seqint57 : seq<int> := [0, 0, 0, 0, 0];
var seqint58 : seq<int> := [0, 0, 0, 0, 0];
var seqint59 : seq<int> := [0, 0, 0, 0, 0];
var seqint60 : seq<int> := [0, 0, 0, 0, 0];
var seqint61 : seq<int> := [0, 0, 0, 0, 0];
var seqint62 : seq<int> := [0, 0, 0, 0, 0];
var seqint63 : seq<int> := [0, 0, 0, 0, 0];
var seqint64 : seq<int> := [0, 0, 0, 0, 0];
var seqint65 : seq<int> := [0, 0, 0, 0, 0];
var seqint66 : seq<int> := [0, 0, 0, 0, 0];
var seqint67 : seq<int> := [0, 0, 0, 0, 0];
var seqint68 : seq<int> := [0, 0, 0, 0, 0];
var seqint69 : seq<int> := [0, 0, 0, 0, 0];
var seqint70 : seq<int> := [0, 0, 0, 0, 0];
var seqint71 : seq<int> := [0, 0, 0, 0, 0];
var seqint72 : seq<int> := [0, 0, 0, 0, 0];
var seqint73 : seq<int> := [0, 0, 0, 0, 0];
var seqint74 : seq<int> := [0, 0, 0, 0, 0];
var seqint75 : seq<int> := [0, 0, 0, 0, 0];
var seqint76 : seq<int> := [0, 0, 0, 0, 0];
var seqint77 : seq<int> := [0, 0, 0, 0, 0];
var seqint78 : seq<int> := [0, 0, 0, 0, 0];
var seqint79 : seq<int> := [0, 0, 0, 0, 0];
var seqint80 : seq<int> := [0, 0, 0, 0, 0];
var seqint81 : seq<int> := [0, 0, 0, 0, 0];
var seqint82 : seq<int> := [0, 0, 0, 0, 0];
var seqint83 : seq<int> := [0, 0, 0, 0, 0];
var seqint84 : seq<int> := [0, 0, 0, 0, 0];
var seqint85 : seq<int> := [0, 0, 0, 0, 0];
var seqint86 : seq<int> := [0, 0, 0, 0, 0];
var seqint87 : seq<int> := [0, 0, 0, 0];
var seqint88 : seq<int> := [0, 0, 0];
var seqint89 : seq<int> := [];
var seqint90 : seq<int> := [0];
var seqint91 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint46, seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83, seqint84, seqint85, seqint86, seqint87, seqint88, seqint89, seqint90, seqint91];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 8 - TIME: 17.506566 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0];
var seqint44 : seq<int> := [0, 0];
var seqint45 : seq<int> := [0];
var seqint46 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46];
var seqint47 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint48 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint49 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint50 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint51 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint52 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint53 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint54 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint55 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint56 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint57 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint58 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint59 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint60 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint61 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint62 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint63 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint64 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint65 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint66 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint67 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint68 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint69 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint70 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint71 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint72 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint73 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint74 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint75 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint76 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint77 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint78 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint79 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint80 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint81 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint82 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint83 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint84 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint85 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint86 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint87 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint88 : seq<int> := [0, 0, 0, 0, 0];
var seqint89 : seq<int> := [0, 0, 0, 0];
var seqint90 : seq<int> := [0, 0, 0];
var seqint91 : seq<int> := [0, 0];
var seqint92 : seq<int> := [0];
var seqint93 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint47, seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83, seqint84, seqint85, seqint86, seqint87, seqint88, seqint89, seqint90, seqint91, seqint92, seqint93];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 9 - TIME: 21.8884106 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0];
var seqint45 : seq<int> := [0, 0];
var seqint46 : seq<int> := [0];
var seqint47 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47];
var seqint48 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint49 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint50 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint51 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint52 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint53 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint54 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint55 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint56 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint57 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint58 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint59 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint60 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint61 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint62 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint63 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint64 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint65 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint66 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint67 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint68 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint69 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint70 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint71 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint72 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint73 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint74 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint75 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint76 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint77 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint78 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint79 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint80 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint81 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint82 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint83 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint84 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint85 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint86 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint87 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint88 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint89 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint90 : seq<int> := [0, 0, 0, 0, 0];
var seqint91 : seq<int> := [0, 0, 0, 0];
var seqint92 : seq<int> := [0, 0, 0];
var seqint93 : seq<int> := [0, 0];
var seqint94 : seq<int> := [0];
var seqint95 : seq<int> := [];
var seqseqint1 : seq<seq<int>> := [seqint48, seqint49, seqint50, seqint51, seqint52, seqint53, seqint54, seqint55, seqint56, seqint57, seqint58, seqint59, seqint60, seqint61, seqint62, seqint63, seqint64, seqint65, seqint66, seqint67, seqint68, seqint69, seqint70, seqint71, seqint72, seqint73, seqint74, seqint75, seqint76, seqint77, seqint78, seqint79, seqint80, seqint81, seqint82, seqint83, seqint84, seqint85, seqint86, seqint87, seqint88, seqint89, seqint90, seqint91, seqint92, seqint93, seqint94, seqint95];
expect |seqseqint0| > 0 && |seqseqint1| > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect |seqseqint0| == |seqseqint1|, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint1[i]|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IndexWiseAddition(seqseqint0, seqseqint1);
expect |r0| == |seqseqint0|;
expect forall i :: 0 <= i < |r0| ==> |r0[i]| == |seqseqint0[i]|;
expect forall i :: 0 <= i < |r0| ==> forall j :: 0 <= j < |r0[i]| ==> r0[i][j] == seqseqint0[i][j] + seqseqint1[i][j];
}

// REPEAT 10 - TIME: 27.1268718 s
