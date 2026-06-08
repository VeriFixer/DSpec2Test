// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test13() {
var seqint0 : seq<int> := [30, 0, 0, 0, 4, 8];
expect 2285 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2285, 5);
expect r0 == seqint0[(5 - 2285 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 10.2890865 s
