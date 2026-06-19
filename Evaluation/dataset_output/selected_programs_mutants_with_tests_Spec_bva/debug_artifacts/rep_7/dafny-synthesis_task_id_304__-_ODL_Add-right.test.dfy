// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test16() {
var seqint0 : seq<int> := [34, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14];
expect 2349 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 24 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2349, 24);
expect r0 == seqint0[(24 - 2349 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 12.070656 s
