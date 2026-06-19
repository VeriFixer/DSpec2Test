// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n - |l|) % |l|];
}


method {:test} Test0() {
var seqint0 : seq<int> := [25];
expect 8365 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8365, 0);
expect r0 == seqint0[(0 - 8365 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.3829471 s

method {:test} Test1() {
var seqint0 : seq<int> := [28, 0, 1];
expect 8366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8366, 2);
expect r0 == seqint0[(2 - 8366 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.1322261 s

method {:test} Test2() {
var seqint0 : seq<int> := [29, 3, 0, 0];
expect 8367 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8367, 3);
expect r0 == seqint0[(3 - 8367 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 4.0193723 s

method {:test} Test3() {
var seqint0 : seq<int> := [27, 0, 0, 0, 0];
expect 8374 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8374, 4);
expect r0 == seqint0[(4 - 8374 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 4.9548305 s

method {:test} Test4() {
var seqint0 : seq<int> := [4, 30, 0, 0, 0, 0];
expect 8380 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8380, 5);
expect r0 == seqint0[(5 - 8380 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 5.7458337 s

method {:test} Test5() {
var seqint0 : seq<int> := [7, 31, 0, 0, 5, 0, 0];
expect 8391 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8391, 6);
expect r0 == seqint0[(6 - 8391 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 6.4185862 s

method {:test} Test6() {
var seqint0 : seq<int> := [6, 0, 26, 0, 0, 0, 0, 0];
expect 8397 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 7 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8397, 7);
expect r0 == seqint0[(7 - 8397 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 7.080777 s

method {:test} Test7() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 33, 0];
expect 8398 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 8 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8398, 8);
expect r0 == seqint0[(8 - 8398 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 7.7910181 s

method {:test} Test8() {
var seqint0 : seq<int> := [11, 0, 0, 9, 0, 0, 0, 32, 0, 0];
expect 8402 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 9 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8402, 9);
expect r0 == seqint0[(9 - 8402 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 8.4234655 s

method {:test} Test9() {
var seqint0 : seq<int> := [21, 36, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 10, 0, 15, 0, 13, 0, 0];
expect 8454 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 27 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8454, 27);
expect r0 == seqint0[(27 - 8454 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 9.0711082 s
