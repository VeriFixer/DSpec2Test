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

method {:test} Test6() {
var seqint0 : seq<int> := [9, 0, 0, 0, 15, 0, 0, 0, 13, 0, 17];
var seqint1 : seq<int> := [0, 4, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 9, 17, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 19];
var seqint1 : seq<int> := [15, 0, 4, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 4 - TIME: 46.891837 s
