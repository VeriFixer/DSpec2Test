// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[(index - n + |l|) / |l|];
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
var seqint0 : seq<int> := [25, 0, 0, 0];
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

// REPEAT 1 - TIME: 8.097626 s

method {:test} Test11() {
var seqint0 : seq<int> := [0, 28, 2];
expect 2283 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2283, 1);
expect r0 == seqint0[(1 - 2283 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 8.9315785 s

method {:test} Test12() {
var seqint0 : seq<int> := [29, 3, 5, 7, 0];
expect 2284 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2284, 4);
expect r0 == seqint0[(4 - 2284 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 9.6135052 s

method {:test} Test13() {
var seqint0 : seq<int> := [30, 0, 0, 0, 4, 8];
expect 2285 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 5 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2285, 5);
expect r0 == seqint0[(5 - 2285 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 10.3312236 s

method {:test} Test14() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0];
expect 2294 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2294, 28);
expect r0 == seqint0[(28 - 2294 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 11.0393012 s

method {:test} Test15() {
var seqint0 : seq<int> := [17, 9, 0, 0, 0, 15, 19, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 34];
expect 2325 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 30 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2325, 30);
expect r0 == seqint0[(30 - 2325 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 12.0354298 s

method {:test} Test16() {
var seqint0 : seq<int> := [18, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 10];
expect 2366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 31 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2366, 31);
expect r0 == seqint0[(31 - 2366 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 13.1445226 s

method {:test} Test17() {
var seqint0 : seq<int> := [20, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0];
expect 2382 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 32 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2382, 32);
expect r0 == seqint0[(32 - 2382 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 14.3200832 s

method {:test} Test18() {
var seqint0 : seq<int> := [35, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 32, 22, 0, 41];
expect 2405 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 36 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2405, 36);
expect r0 == seqint0[(36 - 2405 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 16.1010122 s

method {:test} Test19() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 2464 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 37 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 2464, 37);
expect r0 == seqint0[(37 - 2464 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 17.5370374 s
