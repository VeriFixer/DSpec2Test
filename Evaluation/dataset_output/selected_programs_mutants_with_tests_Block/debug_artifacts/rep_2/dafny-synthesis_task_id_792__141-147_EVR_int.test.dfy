// dafny-synthesis_task_id_792.dfy

method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
  ensures count >= 0
  ensures count == |lists|
{
  count := 0;
}

method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 2 - TIME: 2.9652679 s
