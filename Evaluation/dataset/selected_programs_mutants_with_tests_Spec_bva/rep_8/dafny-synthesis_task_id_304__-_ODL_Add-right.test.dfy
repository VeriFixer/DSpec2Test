// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test17() {
var seqint0 : seq<int> := [20, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0];
expect 2382 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 32 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2382, 32);
expect r0 == seqint0[(32 - 2382 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 14.1198841 s
