// dafny-synthesis_task_id_750.dfy

method {:testEntry} AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
  ensures |r| == |l| + 1
  ensures r[|r| - 1] == t
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
  r := [] + [t];
}

method {:test} Test0() {
var seqint0 : seq<(int, int)> := [];
var int0 : (int, int) := (2,3);
var r0 := AddTupleToList(seqint0, int0);
expect |r0| == |seqint0| + 1;
expect r0[|r0| - 1] == int0;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[i];
}

// REPEAT 1 - TIME: 2.2994882 s
