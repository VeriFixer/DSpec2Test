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

method {:test} Test21() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [0];
var seqint7 : seq<int> := [0];
var seqint8 : seq<int> := [0, 0, 0];
var seqint9 : seq<int> := [0, 1, 0, 0, 0, 0, 0, 0, 0, 3];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9];
var seqint10 : seq<int> := [0, 1, 0, 0, 0, 0, 0, 0, 0, 3];
var r0 := ContainsSequence(seqseqint0, seqint10);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint10 == seqseqint0[i];
}
method {:test} Test22() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0];
var seqint3 : seq<int> := [0];
var seqint4 : seq<int> := [0];
var seqint5 : seq<int> := [0];
var seqint6 : seq<int> := [0];
var seqint7 : seq<int> := [0];
var seqint8 : seq<int> := [0, 0, 0];
var seqint9 : seq<int> := [0];
var seqint10 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10];
var seqint11 : seq<int> := [3, 0, 5, 1];
var r0 := ContainsSequence(seqseqint0, seqint11);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint11 == seqseqint0[i];
}

// REPEAT 2 - TIME: 17.6364089 s
