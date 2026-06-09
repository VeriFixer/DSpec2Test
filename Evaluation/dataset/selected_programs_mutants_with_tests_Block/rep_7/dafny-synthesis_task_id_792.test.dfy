
method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0];
var seqint3 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 7 - TIME: 6.599221 s