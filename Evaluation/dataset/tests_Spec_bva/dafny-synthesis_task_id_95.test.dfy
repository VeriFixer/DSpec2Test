method {:testEntry} SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
{
    v := |s[0]|;
    for i := 1 to |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> v <= |s[k]|
        invariant exists k :: 0 <= k < i && v == |s[k]|
    {
        if |s[i]| < v
        {
            v := |s[i]|;
        }
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}
method {:test} Test2() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 1 - TIME: 4.6815158 s

method {:test} Test6() {
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
var seqint40 : seq<int> := [];
var seqint41 : seq<int> := [];
var seqint42 : seq<int> := [];
var seqint43 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 2 - TIME: 5.6705753 s

method {:test} Test7() {
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
var seqint40 : seq<int> := [0];
var seqint41 : seq<int> := [0];
var seqint42 : seq<int> := [0];
var seqint43 : seq<int> := [0, 0];
var seqint44 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 3 - TIME: 6.6791204 s

method {:test} Test8() {
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
var seqint41 : seq<int> := [0, 0];
var seqint42 : seq<int> := [0, 0];
var seqint43 : seq<int> := [];
var seqint44 : seq<int> := [0];
var seqint45 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 4 - TIME: 8.0502878 s

method {:test} Test9() {
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
var seqint41 : seq<int> := [0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0];
var seqint44 : seq<int> := [0, 0];
var seqint45 : seq<int> := [0];
var seqint46 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 5 - TIME: 9.4456327 s

method {:test} Test10() {
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
var seqint41 : seq<int> := [0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0];
var seqint45 : seq<int> := [0, 0];
var seqint46 : seq<int> := [0];
var seqint47 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 6 - TIME: 11.2213292 s

method {:test} Test11() {
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
var seqint41 : seq<int> := [0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0, 0];
var seqint45 : seq<int> := [0, 0, 0];
var seqint46 : seq<int> := [0, 0];
var seqint47 : seq<int> := [0];
var seqint48 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 7 - TIME: 12.8304642 s

method {:test} Test12() {
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
var seqint41 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0, 0, 0];
var seqint45 : seq<int> := [0, 0, 0, 0];
var seqint46 : seq<int> := [0, 0, 0];
var seqint47 : seq<int> := [0, 0];
var seqint48 : seq<int> := [0];
var seqint49 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 8 - TIME: 14.7927786 s

method {:test} Test13() {
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
var seqint41 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint45 : seq<int> := [0, 0, 0, 0, 0];
var seqint46 : seq<int> := [0, 0, 0, 0];
var seqint47 : seq<int> := [0, 0, 0];
var seqint48 : seq<int> := [0, 0];
var seqint49 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 9 - TIME: 17.1174512 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint34 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint35 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint36 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint37 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint38 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint39 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint40 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint41 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint42 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint43 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint44 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint45 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint46 : seq<int> := [0, 0, 0, 0, 0];
var seqint47 : seq<int> := [0, 0, 0, 0];
var seqint48 : seq<int> := [0, 0, 0];
var seqint49 : seq<int> := [0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36, seqint37, seqint38, seqint39, seqint40, seqint41, seqint42, seqint43, seqint44, seqint45, seqint46, seqint47, seqint48, seqint49];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 10 - TIME: 19.984709 s
