// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n + |l|) / |l|];
}

method {:test} Test0() {
var seqint0 : seq<int> := [26];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.226317 s
