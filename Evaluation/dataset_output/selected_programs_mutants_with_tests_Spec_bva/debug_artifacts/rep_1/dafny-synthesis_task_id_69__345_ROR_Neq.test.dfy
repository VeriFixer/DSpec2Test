// dafny-synthesis_task_id_69.dfy

method {:testEntry} ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |list| && sub == list[i]
{
  result := false;
  for i := 0 to |list|
    invariant 0 <= i <= |list|
    invariant result <==> exists k :: 0 <= k < i && sub == list[k]
  {
    if sub != list[i] {
      result := true;
      break;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8];
var seqint9 : seq<int> := [0];
var r0 := ContainsSequence(seqseqint0, seqint9);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint9 == seqseqint0[i];
}
method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0];
var seqint1 : seq<int> := [0];
var r0 := ContainsSequence(seqseqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint1 == seqseqint0[i];
}
method {:test} Test2() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
var seqint2 : seq<int> := [0];
var r0 := ContainsSequence(seqseqint0, seqint2);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint2 == seqseqint0[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8];
var seqint9 : seq<int> := [];
var r0 := ContainsSequence(seqseqint0, seqint9);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint9 == seqseqint0[i];
}
method {:test} Test5() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [0, 0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8];
var seqint9 : seq<int> := [0, 0];
var r0 := ContainsSequence(seqseqint0, seqint9);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint9 == seqseqint0[i];
}
method {:test} Test10() {
var seqseqint0 : seq<seq<int>> := [];
var seqint0 : seq<int> := [];
var r0 := ContainsSequence(seqseqint0, seqint0);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint0 == seqseqint0[i];
}
method {:test} Test12() {
var seqint0 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0];
var seqint1 : seq<int> := [];
var r0 := ContainsSequence(seqseqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint1 == seqseqint0[i];
}
method {:test} Test13() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1];
var seqint2 : seq<int> := [];
var r0 := ContainsSequence(seqseqint0, seqint2);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint2 == seqseqint0[i];
}
method {:test} Test15() {
var seqseqint0 : seq<seq<int>> := [];
var seqint0 : seq<int> := [0];
var r0 := ContainsSequence(seqseqint0, seqint0);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint0 == seqseqint0[i];
}
method {:test} Test16() {
var seqseqint0 : seq<seq<int>> := [];
var seqint0 : seq<int> := [0, 0];
var r0 := ContainsSequence(seqseqint0, seqint0);
expect r0 <==> exists i :: 0 <= i < |seqseqint0| && seqint0 == seqseqint0[i];
}

// REPEAT 1 - TIME: 15.8103409 s
