// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test7() {
var seqint0 : seq<int> := [20, 0, 35, 10, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 15];
expect 2382 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 14 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2382, 14);
expect r0 == seqint0[(14 - 2382 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 8.6325436 s
