// Prog-Fun-Solutions_tmp_tmp7_gmnz5f_mockExam2_p2.dfy

method {:testEntry} problem2(p: int, q: int, X: int, Y: int)
    returns (r: int, s: int)
  requires p == 2 * X + Y && q == X + 3
  ensures r == X && s == Y
{
  assert p == 2 * X + Y && q == X + 3;
  r, s := p, q;
  assert r == 2 * X + Y && s == X + 3;
  assert r == 2 * X + Y - 2 * X - 6 + 6 && s == X + 3;
  assert r == Y && s == X + 3;
  s := s - 3;
  assert r == Y && s == X;
  r, s := s, r;
  assert s == Y && r == X;
}


method {:test} Test0() {
expect 4868 == 2 * 2434 + 0 && 2437 == 2434 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4868, 2437, 2434, 0);
expect r0 == 2434 && r1 == 0;
}

// REPEAT 1 - TIME: 2.4519575 s

method {:test} Test1() {
expect 4871 == 2 * 2435 + 1 && 2438 == 2435 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4871, 2438, 2435, 1);
expect r0 == 2435 && r1 == 1;
}

// REPEAT 2 - TIME: 3.4989036 s

method {:test} Test2() {
expect 4874 == 2 * 2436 + 2 && 2439 == 2436 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4874, 2439, 2436, 2);
expect r0 == 2436 && r1 == 2;
}

// REPEAT 3 - TIME: 4.4922957 s

method {:test} Test3() {
expect 4877 == 2 * 2437 + 3 && 2440 == 2437 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4877, 2440, 2437, 3);
expect r0 == 2437 && r1 == 3;
}

// REPEAT 4 - TIME: 5.3814894 s

method {:test} Test4() {
expect 4880 == 2 * 2438 + 4 && 2441 == 2438 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4880, 2441, 2438, 4);
expect r0 == 2438 && r1 == 4;
}

// REPEAT 5 - TIME: 6.2681089 s

method {:test} Test5() {
expect 4883 == 2 * 2439 + 5 && 2442 == 2439 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4883, 2442, 2439, 5);
expect r0 == 2439 && r1 == 5;
}

// REPEAT 6 - TIME: 7.2284616 s

method {:test} Test6() {
expect 4886 == 2 * 2440 + 6 && 2443 == 2440 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4886, 2443, 2440, 6);
expect r0 == 2440 && r1 == 6;
}

// REPEAT 7 - TIME: 7.8477085 s

method {:test} Test7() {
expect 4889 == 2 * 2441 + 7 && 2444 == 2441 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4889, 2444, 2441, 7);
expect r0 == 2441 && r1 == 7;
}

// REPEAT 8 - TIME: 8.5219239 s

method {:test} Test8() {
expect 4892 == 2 * 2442 + 8 && 2445 == 2442 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4892, 2445, 2442, 8);
expect r0 == 2442 && r1 == 8;
}

// REPEAT 9 - TIME: 9.2771369 s

method {:test} Test9() {
expect 4895 == 2 * 2443 + 9 && 2446 == 2443 + 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := problem2(4895, 2446, 2443, 9);
expect r0 == 2443 && r1 == 9;
}

// REPEAT 10 - TIME: 9.8325265 s
