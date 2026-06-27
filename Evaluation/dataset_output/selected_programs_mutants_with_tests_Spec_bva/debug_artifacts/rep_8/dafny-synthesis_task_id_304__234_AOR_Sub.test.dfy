// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n - |l|) % |l|];
}

method {:test} Test17() {
var seqint0 : seq<int> := [41, 12, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 24, 0, 39, 33, 22, 0, 0, 0, 0, 20, 36];
expect 2378 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2378, 28);
expect r0 == seqint0[(28 - 2378 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 13.8181949 s
