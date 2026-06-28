// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n + |l|) * |l|];
}


method {:test} Test0() {
var seqint0 : seq<int> := [26];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}
method {:test} Test1() {
var seqint0 : seq<int> := [26];
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 38, 0);
expect r0 == seqint0[(0 - 38 + |seqint0|) % |seqint0|];
}
method {:test} Test2() {
var seqint0 : seq<int> := [26, 0];
expect 1218 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 1218, 0);
expect r0 == seqint0[(0 - 1218 + |seqint0|) % |seqint0|];
}
method {:test} Test3() {
var seqint0 : seq<int> := [25];
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 0, 0);
expect r0 == seqint0[(0 - 0 + |seqint0|) % |seqint0|];
}
method {:test} Test4() {
var seqint0 : seq<int> := [25];
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 100, 0);
expect r0 == seqint0[(0 - 100 + |seqint0|) % |seqint0|];
}
method {:test} Test5() {
var seqint0 : seq<int> := [25];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}
method {:test} Test7() {
var seqint0 : seq<int> := [-100];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}
method {:test} Test8() {
var seqint0 : seq<int> := [100];
expect 2282 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2282, 0);
expect r0 == seqint0[(0 - 2282 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 9.8040626 s

method {:test} Test11() {
var seqint0 : seq<int> := [0, 2, 28];
expect 2283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2283, 2);
expect r0 == seqint0[(2 - 2283 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 11.2684268 s

method {:test} Test12() {
var seqint0 : seq<int> := [5, 29, 0, 3];
expect 2286 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2286, 3);
expect r0 == seqint0[(3 - 2286 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 12.4208014 s

method {:test} Test13() {
var seqint0 : seq<int> := [7, 4, 0, 9, 0, 30];
expect 2292 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2292, 5);
expect r0 == seqint0[(5 - 2292 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 13.5613184 s

method {:test} Test14() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 31];
expect 2296 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 6 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2296, 6);
expect r0 == seqint0[(6 - 2296 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 14.7122298 s

method {:test} Test15() {
var seqint0 : seq<int> := [15, 8, 0, 11, 0, 32, 0, 13];
expect 2306 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 7 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2306, 7);
expect r0 == seqint0[(7 - 2306 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 15.7444539 s

method {:test} Test16() {
var seqint0 : seq<int> := [34, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14];
expect 2349 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 24 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2349, 24);
expect r0 == seqint0[(24 - 2349 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 16.7216609 s

method {:test} Test17() {
var seqint0 : seq<int> := [41, 12, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 24, 0, 39, 33, 22, 0, 0, 0, 0, 20, 36];
expect 2378 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2378, 28);
expect r0 == seqint0[(28 - 2378 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 17.7415231 s

method {:test} Test18() {
var seqint0 : seq<int> := [51, 16, 0, 42, 0, 0, 21, 0, 0, 38, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 47, 0, 43, 49, 0, 0, 0, 45, 0];
expect 2426 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 29 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2426, 29);
expect r0 == seqint0[(29 - 2426 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 18.7336761 s

method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 44, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 19, 0, 0, 0, 53, 50];
expect 2450 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 25 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2450, 25);
expect r0 == seqint0[(25 - 2450 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 19.7910049 s
