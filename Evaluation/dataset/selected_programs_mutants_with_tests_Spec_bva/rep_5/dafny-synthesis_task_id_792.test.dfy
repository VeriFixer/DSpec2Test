
method {:test} Test11() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 5 - TIME: 9.1902067 s