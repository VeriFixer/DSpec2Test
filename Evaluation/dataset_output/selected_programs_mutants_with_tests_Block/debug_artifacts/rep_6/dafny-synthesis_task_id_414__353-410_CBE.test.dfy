// dafny-synthesis_task_id_414.dfy

method {:testEntry} AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |seq1| && seq1[i] in seq2
{
  result := false;
  for i := 0 to |seq1|
    invariant 0 <= i <= |seq1|
    invariant result <==> exists k :: 0 <= k < i && seq1[k] in seq2
  {
    result := true;
    break;
  }
}

method {:test} Test5() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 33];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 16, 0, 0, 20, 23, 0, 0, 0, 8, 0, 29];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 6 - TIME: 7.7372072 s
