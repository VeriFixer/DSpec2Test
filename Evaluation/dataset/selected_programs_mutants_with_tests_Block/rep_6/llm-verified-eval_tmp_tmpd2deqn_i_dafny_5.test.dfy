
method {:test} Test10() {
var seqint0 : seq<int> := [6];
var r0 := intersperse(seqint0, 46);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 46;
}
method {:test} Test11() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 9, 13, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15];
var r0 := intersperse(seqint0, 47);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 47;
}

// REPEAT 6 - TIME: 8.9644145 s