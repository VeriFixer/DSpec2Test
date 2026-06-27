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

method {:test} Test14() {
var seqint0 : seq<int> := [50, 0, 0, 45, 19];
var seqint1 : seq<int> := [0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 19, 31, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 48, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test15() {
var seqint0 : seq<int> := [50, 0, 0, 41, 37];
var seqint1 : seq<int> := [48, 0, 0, 0, 0, 0, 19, 0, 0, 0, 45, 31, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 8 - TIME: 13.982056 s
