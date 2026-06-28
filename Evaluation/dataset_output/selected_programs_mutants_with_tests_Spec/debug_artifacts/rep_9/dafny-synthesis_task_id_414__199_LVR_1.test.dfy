// dafny-synthesis_task_id_414.dfy

method {:testEntry} AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |seq1| && seq1[i] in seq2
{
  result := false;
  for i := 1 to |seq1|
    invariant 0 <= i <= |seq1|
    invariant result <==> exists k :: 0 <= k < i && seq1[k] in seq2
  {
    if seq1[i] in seq2 {
      result := true;
      break;
    }
  }
}

method {:test} Test16() {
var seqint0 : seq<int> := [65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 61, 59, 63];
var seqint1 : seq<int> := [0, 0, 0, 0, 47, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 51, 39, 0, 0, 0, 0, 53];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 39, 0, 0, 47, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 63, 0, 65];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 59, 0, 55, 0, 0, 0, 57, 51, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 9 - TIME: 15.5420632 s
