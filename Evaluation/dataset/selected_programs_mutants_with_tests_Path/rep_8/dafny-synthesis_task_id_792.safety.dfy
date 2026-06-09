method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
{
    count := |lists|;
}

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 8 - TIME: 6.4908827 s
