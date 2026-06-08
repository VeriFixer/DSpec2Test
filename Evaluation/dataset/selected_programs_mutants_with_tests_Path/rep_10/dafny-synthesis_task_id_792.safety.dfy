method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
{
    count := |lists|;
}

method {:test} Test9() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 10 - TIME: 11.818789 s
