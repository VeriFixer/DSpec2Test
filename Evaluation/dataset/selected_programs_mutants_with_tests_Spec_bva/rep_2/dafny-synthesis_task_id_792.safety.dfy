method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
{
    count := |lists|;
}

method {:test} Test8() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 2 - TIME: 5.4999185 s
