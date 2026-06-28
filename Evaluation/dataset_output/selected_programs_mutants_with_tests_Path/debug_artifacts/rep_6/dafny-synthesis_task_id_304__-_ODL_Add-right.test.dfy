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
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 31, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8423 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 29 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8423, 29);
expect r0 == seqint0[(29 - 8423 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 7.9123317 s
