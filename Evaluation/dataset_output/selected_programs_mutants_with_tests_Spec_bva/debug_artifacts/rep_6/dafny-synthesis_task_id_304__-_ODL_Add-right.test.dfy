// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test15() {
var seqint0 : seq<int> := [17, 9, 0, 0, 0, 15, 19, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 34];
expect 2325 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 30 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2325, 30);
expect r0 == seqint0[(30 - 2325 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 12.0354298 s
