// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 44, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 19, 0, 0, 0, 53, 50];
expect 2450 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 25 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2450, 25);
expect r0 == seqint0[(25 - 2450 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 14.4621693 s
