// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[|l| % |l|];
}

method {:test} Test1() {
var seqint0 : seq<int> := [28, 0, 1];
expect 8366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8366, 2);
expect r0 == seqint0[(2 - 8366 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.6198459 s
