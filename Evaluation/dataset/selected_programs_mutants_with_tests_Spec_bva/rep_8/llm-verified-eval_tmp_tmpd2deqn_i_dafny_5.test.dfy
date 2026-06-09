
method {:test} Test18() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 15, 17, 19];
var r0 := intersperse(seqint0, 31);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 31;
}

// REPEAT 8 - TIME: 11.4677734 s