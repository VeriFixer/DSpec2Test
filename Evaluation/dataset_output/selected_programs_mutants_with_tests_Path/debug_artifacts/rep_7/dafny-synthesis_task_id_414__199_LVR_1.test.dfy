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

method {:test} Test12() {
var seqint0 : seq<int> := [0, 0, 0, 16, 0, 27, 0, 0, 0, 0, 0, 0, 35, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 16, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 55, 51, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 61];
var seqint1 : seq<int> := [0, 0, 0, 0, 27, 0, 35, 0, 16, 0, 0, 47, 0, 39, 0, 0, 57, 59];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 7 - TIME: 85.1338344 s
