// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test8() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 12, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 16];
expect 8505 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 27 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8505, 27);
expect r0 == seqint0[(27 - 8505 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 11.2176907 s
