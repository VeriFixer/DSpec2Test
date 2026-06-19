// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n - |l|) % |l|];
}

method {:test} Test14() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 31];
expect 2296 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2296, 6);
expect r0 == seqint0[(6 - 2296 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 10.7232955 s
