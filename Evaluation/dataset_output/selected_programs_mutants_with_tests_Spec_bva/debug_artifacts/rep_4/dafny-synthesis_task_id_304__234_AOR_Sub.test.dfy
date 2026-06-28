// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n - |l|) % |l|];
}

method {:test} Test13() {
var seqint0 : seq<int> := [7, 4, 0, 9, 0, 30];
expect 2292 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2292, 5);
expect r0 == seqint0[(5 - 2292 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 13.5613184 s
