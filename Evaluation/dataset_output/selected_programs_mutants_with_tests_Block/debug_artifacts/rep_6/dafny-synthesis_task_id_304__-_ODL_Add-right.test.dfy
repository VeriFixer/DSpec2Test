// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test5() {
var seqint0 : seq<int> := [7, 31, 0, 0, 5, 0, 0];
expect 8391 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8391, 6);
expect r0 == seqint0[(6 - 8391 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 6.1678795 s
