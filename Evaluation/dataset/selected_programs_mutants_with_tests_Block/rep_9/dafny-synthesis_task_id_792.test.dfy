
method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0];
var seqint3 : seq<int> := [0, 0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 9 - TIME: 8.17037 s