// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n) * |l| % |l|];
}


method {:test} Test0() {
var seqint0 : seq<int> := [26];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.5337115 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 27];
expect 2284 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2284, 1);
expect r0 == seqint0[(1 - 2284 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.3640434 s

method {:test} Test2() {
var seqint0 : seq<int> := [28, 0, 0];
expect 2285 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2285, 2);
expect r0 == seqint0[(2 - 2285 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 4.363985 s

method {:test} Test3() {
var seqint0 : seq<int> := [4, 2, 0, 29];
expect 2288 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2288, 3);
expect r0 == seqint0[(3 - 2288 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 5.2179969 s

method {:test} Test4() {
var seqint0 : seq<int> := [8, 6, 0, 30, 3];
expect 2291 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2291, 4);
expect r0 == seqint0[(4 - 2291 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 6.1202623 s

method {:test} Test5() {
var seqint0 : seq<int> := [5, 9, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0];
expect 2324 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2324, 28);
expect r0 == seqint0[(28 - 2324 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 6.9796674 s

method {:test} Test6() {
var seqint0 : seq<int> := [7, 12, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16];
expect 2359 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 29 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2359, 29);
expect r0 == seqint0[(29 - 2359 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 7.8940175 s

method {:test} Test7() {
var seqint0 : seq<int> := [20, 0, 35, 10, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 15];
expect 2382 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 14 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2382, 14);
expect r0 == seqint0[(14 - 2382 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 8.6325436 s

method {:test} Test8() {
var seqint0 : seq<int> := [31, 13, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 22, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 19];
expect 2397 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 15 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2397, 15);
expect r0 == seqint0[(15 - 2397 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 9.3671579 s

method {:test} Test9() {
var seqint0 : seq<int> := [41, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 39];
expect 2409 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 16 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2409, 16);
expect r0 == seqint0[(16 - 2409 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 9.9546372 s
