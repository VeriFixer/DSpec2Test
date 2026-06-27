// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n - |l|) % |l|];
}

method {:test} Test8() {
var seqint0 : seq<int> := [11, 0, 0, 9, 0, 0, 0, 32, 0, 0];
expect 8402 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 9 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8402, 9);
expect r0 == seqint0[(9 - 8402 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 8.9870907 s
