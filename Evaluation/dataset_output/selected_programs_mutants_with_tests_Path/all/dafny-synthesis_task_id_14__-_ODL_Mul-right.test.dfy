// dafny-synthesis_task_id_14.dfy

method {:testEntry} TriangularPrismVolume(base: int, height: int, length: int)
    returns (volume: int)
  requires base > 0
  requires height > 0
  requires length > 0
  ensures volume == base * height * length / 2
{
  volume := base / 2;
}


method {:test} Test0() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(2, 1, 1);
expect r0 == 2 * 1 * 1 / 2;
}

// REPEAT 1 - TIME: 3.2499665 s

method {:test} Test1() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(3, 2, 2);
expect r0 == 3 * 2 * 2 / 2;
}

// REPEAT 2 - TIME: 4.3646582 s

method {:test} Test2() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(4, 3, 3);
expect r0 == 4 * 3 * 3 / 2;
}

// REPEAT 3 - TIME: 5.6227776 s

method {:test} Test3() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5924 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(5, 4, 5924);
expect r0 == 5 * 4 * 5924 / 2;
}

// REPEAT 4 - TIME: 6.6912472 s

method {:test} Test4() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5925 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(6, 5, 5925);
expect r0 == 6 * 5 * 5925 / 2;
}

// REPEAT 5 - TIME: 7.7115084 s

method {:test} Test5() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5926 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(7, 6, 5926);
expect r0 == 7 * 6 * 5926 / 2;
}

// REPEAT 6 - TIME: 8.507972 s

method {:test} Test6() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5927 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(8, 7, 5927);
expect r0 == 8 * 7 * 5927 / 2;
}

// REPEAT 7 - TIME: 9.2986798 s

method {:test} Test7() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(9, 8, 5928);
expect r0 == 9 * 8 * 5928 / 2;
}

// REPEAT 8 - TIME: 10.2179403 s

method {:test} Test8() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5929 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(10, 9, 5929);
expect r0 == 10 * 9 * 5929 / 2;
}

// REPEAT 9 - TIME: 11.1670708 s

method {:test} Test9() {
expect 11 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5930 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(11, 10, 5930);
expect r0 == 11 * 10 * 5930 / 2;
}

// REPEAT 10 - TIME: 12.1243252 s
