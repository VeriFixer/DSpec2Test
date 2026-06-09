// dafny-synthesis_task_id_586.dfy

method {:testEntry} SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0 && n < |l|
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
{
  var secondPart: seq<int> := l[n..];
  var firstPart: seq<int> := l[..n];
  r := secondPart + firstPart;
}

method {:test} Test11() {
var seqint0 : seq<int> := [7, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
expect 3 >= 0 && 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SplitAndAppend(seqint0, 3);
expect |r0| == |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[i] == seqint0[(i + 3) % |seqint0|];
}

// REPEAT 4 - TIME: 8.951393 s
