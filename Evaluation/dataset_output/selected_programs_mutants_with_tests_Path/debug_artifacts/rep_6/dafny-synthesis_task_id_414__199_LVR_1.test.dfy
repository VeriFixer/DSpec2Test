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

method {:test} Test10() {
var seqint0 : seq<int> := [0, 0, 33, 0, 0, 0, 0, 20, 36, 0, 0, 38, 40];
var seqint1 : seq<int> := [11, 0, 25, 29, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test11() {
var seqint0 : seq<int> := [44, 0, 0, 11, 0, 0, 40, 36, 0, 38, 42, 20];
var seqint1 : seq<int> := [46, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 29, 0, 0, 0, 33, 11];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 6 - TIME: 71.0890652 s
