
method {:test} Test16() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 10 - TIME: 12.7316883 s