// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test6() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2394 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 32 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2394, 32);
expect r0 == seqint0[(32 - 2394 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 7.8884469 s
