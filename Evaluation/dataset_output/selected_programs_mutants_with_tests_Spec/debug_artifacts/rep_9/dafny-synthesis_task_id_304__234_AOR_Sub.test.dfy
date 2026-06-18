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
var seqint0 : seq<int> := [31, 13, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 22, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 19];
expect 2397 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 15 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2397, 15);
expect r0 == seqint0[(15 - 2397 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 9.341321 s
