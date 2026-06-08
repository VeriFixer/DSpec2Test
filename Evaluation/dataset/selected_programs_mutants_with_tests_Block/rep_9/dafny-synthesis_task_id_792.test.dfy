
method {:test} Test8() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 9 - TIME: 8.3690863 s