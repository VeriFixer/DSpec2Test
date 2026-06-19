// dafny-synthesis_task_id_792.dfy

method {:testEntry} CountLists(lists: seq<seq<int>>) returns (count: int)
  ensures count >= 0
  ensures count == |lists|
{
  count := 0;
}

method {:test} Test0() {
var seqseqint0 : seq<seq<int>> := [];
var r0 := CountLists(seqseqint0);
expect r0 >= 0;
expect r0 == |seqseqint0|;
}

// REPEAT 1 - TIME: 1.3767392 s
