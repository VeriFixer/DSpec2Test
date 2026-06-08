method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
{
    count := |lists|;
}

method {:test} Test5() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 6 - TIME: 7.1954771 s
