// dafny-synthesis_task_id_14.dfy

method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int)
    returns (volume: int)
  requires base > 0
  requires height > 0
  requires length > 0
  ensures volume == base * height * length / 2
{
  volume := base * height * length % 2;
}


method {:test} Test0() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(2, 1, 1);
expect r0 == 2 * 1 * 1 / 2;
}
method {:test} Test1() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(1, 1, 1);
expect r0 == 1 * 1 * 1 / 2;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(100, 1, 1);
expect r0 == 100 * 1 * 1 / 2;
}
method {:test} Test4() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(1, 100, 1);
expect r0 == 1 * 100 * 1 / 2;
}
method {:test} Test6() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(1, 1, 100);
expect r0 == 1 * 1 * 100 / 2;
}
method {:test} Test8() {
expect 200 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(200, 1, 1);
expect r0 == 200 * 1 * 1 / 2;
}

// REPEAT 1 - TIME: 9.7156341 s

method {:test} Test11() {
expect 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(201, 101, 101);
expect r0 == 201 * 101 * 101 / 2;
}

// REPEAT 2 - TIME: 10.9529537 s

method {:test} Test12() {
expect 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1425 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(202, 102, 1425);
expect r0 == 202 * 102 * 1425 / 2;
}

// REPEAT 3 - TIME: 11.8964377 s

method {:test} Test13() {
expect 203 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1426 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(203, 103, 1426);
expect r0 == 203 * 103 * 1426 / 2;
}

// REPEAT 4 - TIME: 12.7990246 s

method {:test} Test14() {
expect 204 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1427 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(204, 104, 1427);
expect r0 == 204 * 104 * 1427 / 2;
}

// REPEAT 5 - TIME: 13.697238 s

method {:test} Test15() {
expect 205 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1428 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(205, 105, 1428);
expect r0 == 205 * 105 * 1428 / 2;
}

// REPEAT 6 - TIME: 14.8159531 s

method {:test} Test16() {
expect 206 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1429 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(206, 106, 1429);
expect r0 == 206 * 106 * 1429 / 2;
}

// REPEAT 7 - TIME: 15.8537688 s

method {:test} Test17() {
expect 207 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1430 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(207, 107, 1430);
expect r0 == 207 * 107 * 1430 / 2;
}

// REPEAT 8 - TIME: 16.8130804 s

method {:test} Test18() {
expect 208 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1431 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(208, 108, 1431);
expect r0 == 208 * 108 * 1431 / 2;
}

// REPEAT 9 - TIME: 17.7506108 s

method {:test} Test19() {
expect 209 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1432 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(209, 109, 1432);
expect r0 == 209 * 109 * 1432 / 2;
}

// REPEAT 10 - TIME: 18.5690519 s
