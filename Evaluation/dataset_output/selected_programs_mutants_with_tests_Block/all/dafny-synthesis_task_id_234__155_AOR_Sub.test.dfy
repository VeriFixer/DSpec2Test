// dafny-synthesis_task_id_234.dfy

method {:testEntry} CubeVolume(size: int) returns (volume: int)
  requires size > 0
  ensures volume == size * size * size
{
  volume := size * size - size;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(1);
expect r0 == 1 * 1 * 1;
}

// REPEAT 1 - TIME: 2.1907622 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(2);
expect r0 == 2 * 2 * 2;
}

// REPEAT 2 - TIME: 3.0918714 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(3);
expect r0 == 3 * 3 * 3;
}

// REPEAT 3 - TIME: 3.9090888 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(4);
expect r0 == 4 * 4 * 4;
}

// REPEAT 4 - TIME: 4.8168517 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(5);
expect r0 == 5 * 5 * 5;
}

// REPEAT 5 - TIME: 5.6271832 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(6);
expect r0 == 6 * 6 * 6;
}

// REPEAT 6 - TIME: 6.3013192 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(7);
expect r0 == 7 * 7 * 7;
}

// REPEAT 7 - TIME: 6.9071561 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(8);
expect r0 == 8 * 8 * 8;
}

// REPEAT 8 - TIME: 7.5778846 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(9);
expect r0 == 9 * 9 * 9;
}

// REPEAT 9 - TIME: 8.0784592 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(10);
expect r0 == 10 * 10 * 10;
}

// REPEAT 10 - TIME: 8.6272112 s
