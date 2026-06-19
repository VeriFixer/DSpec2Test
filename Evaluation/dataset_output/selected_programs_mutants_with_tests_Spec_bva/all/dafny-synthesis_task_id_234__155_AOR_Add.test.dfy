// dafny-synthesis_task_id_234.dfy

method {:testEntry} CubeVolume(size: int) returns (volume: int)
  requires size > 0
  ensures volume == size * size * size
{
  volume := size * size + size;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(1);
expect r0 == 1 * 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(100);
expect r0 == 100 * 100 * 100;
}

// REPEAT 1 - TIME: 5.817853 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(101);
expect r0 == 101 * 101 * 101;
}

// REPEAT 2 - TIME: 6.6513482 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(102);
expect r0 == 102 * 102 * 102;
}

// REPEAT 3 - TIME: 7.4928481 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(103);
expect r0 == 103 * 103 * 103;
}

// REPEAT 4 - TIME: 8.259806 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(104);
expect r0 == 104 * 104 * 104;
}

// REPEAT 5 - TIME: 8.9386145 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(105);
expect r0 == 105 * 105 * 105;
}

// REPEAT 6 - TIME: 9.5761697 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(106);
expect r0 == 106 * 106 * 106;
}

// REPEAT 7 - TIME: 10.2210112 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(107);
expect r0 == 107 * 107 * 107;
}

// REPEAT 8 - TIME: 10.7846308 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(108);
expect r0 == 108 * 108 * 108;
}

// REPEAT 9 - TIME: 11.4386882 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(109);
expect r0 == 109 * 109 * 109;
}

// REPEAT 10 - TIME: 12.0584824 s
