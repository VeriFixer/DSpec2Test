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
var seqint0 : seq<int> := [18, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 10];
expect 2366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 31 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2366, 31);
expect r0 == seqint0[(31 - 2366 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 13.1049978 s
