// dafny-synthesis_task_id_14.dfy

method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int)
    returns (volume: int)
  requires base > 0
  requires height > 0
  requires length > 0
  ensures volume == base * height * length / 2
{
  volume := 2;
}


method {:test} Test0() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(2, 1, 1);
expect r0 == 2 * 1 * 1 / 2;
}

// REPEAT 1 - TIME: 2.767347 s

method {:test} Test1() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(3, 2, 2);
expect r0 == 3 * 2 * 2 / 2;
}

// REPEAT 2 - TIME: 3.6521835 s

method {:test} Test2() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(4, 3, 3);
expect r0 == 4 * 3 * 3 / 2;
}

// REPEAT 3 - TIME: 4.6344954 s

method {:test} Test3() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(5, 4, 4);
expect r0 == 5 * 4 * 4 / 2;
}

// REPEAT 4 - TIME: 5.4532185 s

method {:test} Test4() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(6, 5, 5);
expect r0 == 6 * 5 * 5 / 2;
}

// REPEAT 5 - TIME: 6.5209417 s

method {:test} Test5() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1659 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(7, 6, 1659);
expect r0 == 7 * 6 * 1659 / 2;
}

// REPEAT 6 - TIME: 7.3249226 s

method {:test} Test6() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1660 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(8, 7, 1660);
expect r0 == 8 * 7 * 1660 / 2;
}

// REPEAT 7 - TIME: 8.0827501 s

method {:test} Test7() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1661 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(9, 8, 1661);
expect r0 == 9 * 8 * 1661 / 2;
}

// REPEAT 8 - TIME: 8.7909362 s

method {:test} Test8() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1662 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(10, 9, 1662);
expect r0 == 10 * 9 * 1662 / 2;
}

// REPEAT 9 - TIME: 9.5618121 s

method {:test} Test9() {
expect 11 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1663 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(11, 10, 1663);
expect r0 == 11 * 10 * 1663 / 2;
}

// REPEAT 10 - TIME: 10.1382634 s
