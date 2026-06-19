// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test9() {
var seqint0 : seq<int> := [41, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 39];
expect 2409 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 16 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2409, 16);
expect r0 == seqint0[(16 - 2409 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 9.9546372 s
