// dafny-synthesis_task_id_95.dfy

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
    if |s[i]| < v {
    }
  }
}


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
var seqint0 : seq<int> := [0, 0];
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
var seqint16 : seq<int> := [0, 0];
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
var seqint27 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 1 - TIME: 2.5294051 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0];
var seqint1 : seq<int> := [0, 0];
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
var seqint16 : seq<int> := [0, 0, 0];
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
var seqint28 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 2 - TIME: 3.6422891 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0];
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
var seqint16 : seq<int> := [];
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
var seqint27 : seq<int> := [];
var seqint28 : seq<int> := [];
var seqint29 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 3 - TIME: 5.1470415 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0];
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
var seqint27 : seq<int> := [0, 0, 0];
var seqint28 : seq<int> := [0, 0];
var seqint29 : seq<int> := [0];
var seqint30 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 4 - TIME: 7.1111428 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0];
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
var seqint27 : seq<int> := [0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0];
var seqint29 : seq<int> := [0, 0];
var seqint30 : seq<int> := [0];
var seqint31 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 5 - TIME: 9.2534159 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0];
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
var seqint27 : seq<int> := [0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0];
var seqint30 : seq<int> := [0, 0];
var seqint31 : seq<int> := [0];
var seqint32 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 6 - TIME: 11.8056473 s

method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
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
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0];
var seqint31 : seq<int> := [0, 0];
var seqint32 : seq<int> := [0];
var seqint33 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 7 - TIME: 13.7784397 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
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
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0];
var seqint32 : seq<int> := [0, 0];
var seqint33 : seq<int> := [0];
var seqint34 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 8 - TIME: 16.0721865 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0];
var seqint33 : seq<int> := [0, 0];
var seqint34 : seq<int> := [0];
var seqint35 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 9 - TIME: 18.4533484 s

method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint4 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint5 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint6 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint7 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint8 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint9 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint10 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint11 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint12 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint13 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint14 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint15 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint16 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint17 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint18 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint19 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint20 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint21 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint22 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint23 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint24 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint25 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint26 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint27 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint28 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0];
var seqint29 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint30 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint31 : seq<int> := [0, 0, 0, 0, 0];
var seqint32 : seq<int> := [0, 0, 0, 0];
var seqint33 : seq<int> := [0, 0, 0];
var seqint34 : seq<int> := [0, 0];
var seqint35 : seq<int> := [0];
var seqint36 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20, seqint21, seqint22, seqint23, seqint24, seqint25, seqint26, seqint27, seqint28, seqint29, seqint30, seqint31, seqint32, seqint33, seqint34, seqint35, seqint36];
expect |seqseqint0| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SmallestListLength(seqseqint0);
expect forall i :: 0 <= i < |seqseqint0| ==> r0 <= |seqseqint0[i]|;
expect exists i :: 0 <= i < |seqseqint0| && r0 == |seqseqint0[i]|;
}

// REPEAT 10 - TIME: 20.9132576 s
