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

method {:test} Test6() {
var seqint0 : seq<int> := [35, 20, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 13, 29];
var seqint1 : seq<int> := [33, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 27];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 7 - TIME: 8.0156958 s
