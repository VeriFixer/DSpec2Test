// dafny-synthesis_task_id_69.dfy

method {:testEntry} ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |list| && sub == list[i]
{
  result := false;
  for i := 0 to |list|
    invariant 0 <= i <= |list|
    invariant result <==> exists k :: 0 <= k < i && sub == list[k]
  {
    if true {
      result := true;
      break;
    }
  }
}

method {:test} Test2() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [3, 0, 0, 0, 0, 1];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [0];
var seqint7 : seq<int> := [0];
var seqint8 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8];
var seqint9 : seq<int> := [3, 0, 0, 0, 0, 1];
var r0 := ContainsSequence(seqseqint0, seqint9);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint9 == seqseqint0[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [0];
var seqint7 : seq<int> := [0];
var seqint8 : seq<int> := [0, 0];
var seqint9 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9];
var seqint10 : seq<int> := [0, 1, 0];
var r0 := ContainsSequence(seqseqint0, seqint10);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint10 == seqseqint0[i];
}

// REPEAT 2 - TIME: 5.1745674 s
