// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[|l| % |l|];
}


method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{
    element := l[(index - n + |l|) % |l|];
}

method {:test} Test0() {
var seqint0 : seq<int> := [26];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 2.226317 s

method {:test} Test1() {
var seqint0 : seq<int> := [27, 1];
expect 2283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2283, 1);
expect r0 == seqint0[(1 - 2283 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 3.1998002 s

method {:test} Test2() {
var seqint0 : seq<int> := [28, 0, 0];
expect 2288 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2288, 2);
expect r0 == seqint0[(2 - 2288 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 4.193989 s

method {:test} Test3() {
var seqint0 : seq<int> := [5, 3, 29, 0];
expect 2289 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2289, 3);
expect r0 == seqint0[(3 - 2289 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 5.0933548 s

method {:test} Test4() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0];
expect 2315 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 25 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2315, 25);
expect r0 == seqint0[(25 - 2315 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 6.009338 s

method {:test} Test5() {
var seqint0 : seq<int> := [6, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
expect 2350 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 27 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2350, 27);
expect r0 == seqint0[(27 - 2350 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 6.8421723 s

method {:test} Test6() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2394 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 32 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2394, 32);
expect r0 == seqint0[(32 - 2394 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 7.6713066 s

method {:test} Test7() {
var seqint0 : seq<int> := [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38];
expect 2415 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 34 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2415, 34);
expect r0 == seqint0[(34 - 2415 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 8.6392321 s

method {:test} Test8() {
var seqint0 : seq<int> := [14, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2479 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 35 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2479, 35);
expect r0 == seqint0[(35 - 2479 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 9.9659674 s

method {:test} Test9() {
var seqint0 : seq<int> := [16, 0, 0, 0, 42, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2548 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 36 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2548, 36);
expect r0 == seqint0[(36 - 2548 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 11.7189791 s
