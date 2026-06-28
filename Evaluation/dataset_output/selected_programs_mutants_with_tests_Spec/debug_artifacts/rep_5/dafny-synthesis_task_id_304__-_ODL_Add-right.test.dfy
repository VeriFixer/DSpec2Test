// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) % |l|];
}

method {:test} Test4() {
var seqint0 : seq<int> := [8, 6, 0, 30, 3];
expect 2291 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2291, 4);
expect r0 == seqint0[(4 - 2291 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 7.0654386 s
