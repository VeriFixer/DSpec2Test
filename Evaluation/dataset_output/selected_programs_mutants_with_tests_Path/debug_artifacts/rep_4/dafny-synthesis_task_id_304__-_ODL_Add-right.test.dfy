// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test3() {
var seqint0 : seq<int> := [27, 0, 0, 0, 0];
expect 8374 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8374, 4);
expect r0 == seqint0[(4 - 8374 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 4.7128822 s
