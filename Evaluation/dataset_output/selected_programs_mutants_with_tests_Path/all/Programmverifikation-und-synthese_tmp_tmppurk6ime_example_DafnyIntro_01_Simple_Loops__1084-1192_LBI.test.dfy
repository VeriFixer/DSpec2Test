// Programmverifikation-und-synthese_tmp_tmppurk6ime_example_DafnyIntro_01_Simple_Loops.dfy

method {:testEntry} Gauss(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * (n + 1) / 2
{
  sum := 0;
  var i := 0;
  while i < n
    invariant sum == i * (i + 1) / 2
    invariant i <= n
  {
    break;
    i := i + 1;
    sum := sum + i;
  }
}

method {:testEntry} sumOdds(n: nat) returns (sum: nat)
  ensures sum == n * n
{
  sum := 0;
  var i := 0;
  while i < n
    invariant sum == i * i
    invariant i <= n
  {
    sum := sum + 2 * i + 1;
    i := i + 1;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(0);
expect r0 == 0 * (0 + 1) / 2;
}
method {:test} Test1() {
var r0 := sumOdds(0);
expect r0 == 0 * 0;
}

// REPEAT 1 - TIME: 10.7777558 s

method {:test} Test2() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(1);
expect r0 == 1 * (1 + 1) / 2;
}
method {:test} Test3() {
var r0 := sumOdds(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 17.5352689 s

method {:test} Test4() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(2);
expect r0 == 2 * (2 + 1) / 2;
}
method {:test} Test5() {
var r0 := sumOdds(2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 24.3610919 s

method {:test} Test6() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(3);
expect r0 == 3 * (3 + 1) / 2;
}
method {:test} Test7() {
var r0 := sumOdds(3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 30.6837685 s

method {:test} Test8() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(4);
expect r0 == 4 * (4 + 1) / 2;
}
method {:test} Test9() {
var r0 := sumOdds(4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 38.4067277 s

method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(5);
expect r0 == 5 * (5 + 1) / 2;
}
method {:test} Test11() {
var r0 := sumOdds(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 46.5817993 s

method {:test} Test12() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(6);
expect r0 == 6 * (6 + 1) / 2;
}
method {:test} Test13() {
var r0 := sumOdds(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 53.4376877 s

method {:test} Test14() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(7);
expect r0 == 7 * (7 + 1) / 2;
}
method {:test} Test15() {
var r0 := sumOdds(7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 60.9730816 s

method {:test} Test16() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(8);
expect r0 == 8 * (8 + 1) / 2;
}
method {:test} Test17() {
var r0 := sumOdds(8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 70.0388794 s

method {:test} Test18() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(9);
expect r0 == 9 * (9 + 1) / 2;
}
method {:test} Test19() {
var r0 := sumOdds(9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 77.3990346 s
