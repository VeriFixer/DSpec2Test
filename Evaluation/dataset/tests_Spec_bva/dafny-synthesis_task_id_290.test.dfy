method {:testEntry} MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
{
    maxList := lists[0];

    for i := 1 to |lists|
        invariant 1 <= i <= |lists|
        invariant forall l :: l in lists[..i] ==> |l| <= |maxList|
        invariant maxList in lists[..i]
    {
        if |lists[i]| > |maxList| {
            maxList := lists[i];
        }
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}
method {:test} Test6() {
var seqint0 : seq<int> := [0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 1 - TIME: 6.5976002 s

method {:test} Test9() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 2 - TIME: 7.544526 s

method {:test} Test10() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0, 0, 0];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 3 - TIME: 8.332459 s

method {:test} Test11() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 4 - TIME: 9.1303264 s

method {:test} Test12() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [0, 0, 0];
var seqint3 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 5 - TIME: 9.8981525 s

method {:test} Test13() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [0, 0, 0, 0];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [];
var seqint9 : seq<int> := [];
var seqint10 : seq<int> := [];
var seqint11 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 6 - TIME: 10.6271776 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 7 - TIME: 11.4237764 s

method {:test} Test15() {
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
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 8 - TIME: 12.3650723 s

method {:test} Test16() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 9 - TIME: 13.1993562 s

method {:test} Test17() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MaxLengthList(seqseqint0);
expect forall l :: l in seqseqint0 ==> |l| <= |r0|;
expect r0 in seqseqint0;
}

// REPEAT 10 - TIME: 14.0735691 s
