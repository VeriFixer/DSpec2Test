// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n + |l|) / |l|];
}

method {:test} Test0() {
var seqint0 : seq<int> := [25];
expect 8365 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8365, 0);
expect r0 == seqint0[(0 - 8365 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.0224337 s
