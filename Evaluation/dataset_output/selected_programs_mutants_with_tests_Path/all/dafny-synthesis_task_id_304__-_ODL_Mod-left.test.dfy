// dafny-synthesis_task_id_304.dfy

method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  requires n >= 0
  requires 0 <= index < |l|
  ensures element == l[(index - n + |l|) % |l|]
{
  element := l[|l|];
}


method {:testEntry} ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{
    element := l[(index - n + |l|) % |l|];
}

method {:test} Test0() {
var seqint0 : seq<int> := [25];
expect 8365 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 0 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8365, 0);
expect r0 == seqint0[(0 - 8365 + |seqint0|) % |seqint0|];
}

// REPEAT 1 - TIME: 1.2522185 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 28];
expect 8366 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 1 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8366, 1);
expect r0 == seqint0[(1 - 8366 + |seqint0|) % |seqint0|];
}

// REPEAT 2 - TIME: 1.6651197 s

method {:test} Test2() {
var seqint0 : seq<int> := [26, 2, 0];
expect 8369 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 2 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8369, 2);
expect r0 == seqint0[(2 - 8369 + |seqint0|) % |seqint0|];
}

// REPEAT 3 - TIME: 2.1073437 s

method {:test} Test3() {
var seqint0 : seq<int> := [3, 29, 0, 0];
expect 8370 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 3 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8370, 3);
expect r0 == seqint0[(3 - 8370 + |seqint0|) % |seqint0|];
}

// REPEAT 4 - TIME: 2.55996 s

method {:test} Test4() {
var seqint0 : seq<int> := [4, 0, 0, 27, 6];
expect 8371 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 4 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8371, 4);
expect r0 == seqint0[(4 - 8371 + |seqint0|) % |seqint0|];
}

// REPEAT 5 - TIME: 3.0393772 s

method {:test} Test5() {
var seqint0 : seq<int> := [10, 5, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8];
expect 8420 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 26 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8420, 26);
expect r0 == seqint0[(26 - 8420 + |seqint0|) % |seqint0|];
}

// REPEAT 6 - TIME: 3.5874985 s

method {:test} Test6() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8462 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 28 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8462, 28);
expect r0 == seqint0[(28 - 8462 + |seqint0|) % |seqint0|];
}

// REPEAT 7 - TIME: 4.0879813 s

method {:test} Test7() {
var seqint0 : seq<int> := [9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8508 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 29 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8508, 29);
expect r0 == seqint0[(29 - 8508 + |seqint0|) % |seqint0|];
}

// REPEAT 8 - TIME: 4.6696947 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 14, 0, 11, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 39];
expect 8510 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 36 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8510, 36);
expect r0 == seqint0[(36 - 8510 + |seqint0|) % |seqint0|];
}

// REPEAT 9 - TIME: 5.6200808 s

method {:test} Test9() {
var seqint0 : seq<int> := [42, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 8511 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 <= 37 < |seqint0|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ElementAtIndexAfterRotation(seqint0, 8511, 37);
expect r0 == seqint0[(37 - 8511 + |seqint0|) % |seqint0|];
}

// REPEAT 10 - TIME: 6.1061998 s
