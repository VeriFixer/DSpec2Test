
method {:test} Test14() {
var seqint0 : seq<int> := [10, 0, 0, 17, 21];
var r0 := intersperse(seqint0, 50);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 50;
}
method {:test} Test15() {
var seqint0 : seq<int> := [10, 0, 17, 0, 0, 0, 0, 0, 21, 0, 0, 0, 24];
var r0 := intersperse(seqint0, 50);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 50;
}

// REPEAT 8 - TIME: 11.6900952 s