
method {:test} Test3() {
var seqint0 : seq<int> := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 27);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 27;
}

// REPEAT 4 - TIME: 5.5454323 s