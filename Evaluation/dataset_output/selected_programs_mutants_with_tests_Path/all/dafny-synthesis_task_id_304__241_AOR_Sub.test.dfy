// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[index - n + |l| - |l|];
}


method {:test} Test0() {
var seqint0 : seq<int> := [25];
expect 8365 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8365, 0);
expect r0 == seqint0[(0 - 8365 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.5628814 s

method {:test} Test1() {
var seqint0 : seq<int> := [28, 0, 1];
expect 8366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8366, 2);
expect r0 == seqint0[(2 - 8366 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.6198459 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 27, 3, 0];
expect 8370 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8370, 3);
expect r0 == seqint0[(3 - 8370 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 4.7000843 s

method {:test} Test3() {
var seqint0 : seq<int> := [4, 0, 0, 29, 0];
expect 8371 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8371, 4);
expect r0 == seqint0[(4 - 8371 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 5.8350552 s

method {:test} Test4() {
var seqint0 : seq<int> := [7, 5, 0, 30, 0, 0];
expect 8372 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8372, 5);
expect r0 == seqint0[(5 - 8372 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 6.9345949 s

method {:test} Test5() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 31, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8423 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 29 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8423, 29);
expect r0 == seqint0[(29 - 8423 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 7.9123317 s

method {:test} Test6() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 8, 0, 34];
expect 8424 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 7 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8424, 7);
expect r0 == seqint0[(7 - 8424 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 8.9929319 s

method {:test} Test7() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 13, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0];
expect 8469 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 26 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8469, 26);
expect r0 == seqint0[(26 - 8469 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 10.1299621 s

method {:test} Test8() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 12, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 16];
expect 8505 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 27 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8505, 27);
expect r0 == seqint0[(27 - 8505 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 11.2176907 s

method {:test} Test9() {
var seqint0 : seq<int> := [41, 0, 0, 38, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 20, 0, 23, 39, 26];
expect 8545 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8545, 28);
expect r0 == seqint0[(28 - 8545 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 12.2246432 s
