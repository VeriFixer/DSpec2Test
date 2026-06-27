// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n - |l|) % |l|];
}

method {:test} Test4() {
var seqint0 : seq<int> := [4, 30, 0, 0, 0, 0];
expect 8380 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8380, 5);
expect r0 == seqint0[(5 - 8380 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 5.6504344 s
