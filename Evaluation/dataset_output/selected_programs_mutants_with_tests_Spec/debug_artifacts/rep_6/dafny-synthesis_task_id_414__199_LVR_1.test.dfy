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
var seqint0 : seq<int> := [32, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 17, 0, 0, 0, 25, 0];
var seqint1 : seq<int> := [30, 10, 0, 28];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test11() {
var seqint0 : seq<int> := [34, 0, 0, 0, 0, 17, 0, 21, 0, 30];
var seqint1 : seq<int> := [32, 0, 0, 25, 28, 10];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 6 - TIME: 11.2691802 s
