// ProjectosCVS_tmp_tmp_02_gmcw_Handout 1_CVS_handout1_55754_55780.dfy

lemma peasantMultLemma(a: int, b: int)
  requires b >= 0
  ensures b % 2 == 0 ==> a * b == 2 * a * b / 2
  ensures b % 2 == 1 ==> a * b == a + 2 * a * (b - 1) / 2
{
  if b % 2 == 0 && b > 0 {
    peasantMultLemma(a, b - 2);
  }
  if b % 2 == 1 && b > 1 {
    peasantMultLemma(a, b - 2);
  }
}

method {:testEntry} peasantMult(a: int, b: int) returns (r: int)
  requires b > 0
  ensures r == a * b
{
  r := 0;
  var aa := a;
  var bb := b;
  while bb >= 0
    invariant 0 <= bb <= b
    invariant r + aa * bb == a * b
    decreases bb
  {
    if bb % 2 == 0 {
      aa := 2 * aa;
      bb := bb / 2;
    } else if bb % 2 == 1 {
      r := r + aa;
      aa := 2 * aa;
      bb := (bb - 1) / 2;
    }
  }
}

method {:testEntry} euclidianDiv(a: int, b: int)
    returns (q: int, r: int)
  requires a >= 0
  requires b > 0
  ensures a == b * q + r
{
  r := a;
  q := 0;
  while r - b >= 0
    invariant 0 <= r <= a
    invariant r == a - b * q
    decreases r - b
  {
    r := r - b;
    q := q + 1;
  }
}


method {:test} Test0() {
expect 450 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(0, 450);
expect r0 == 0 * 450;
}
method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1, 2);
expect r0 == 1 * 2;
}
method {:test} Test2() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(1, 1);
expect 1 == 1 * r0 + r1;
}

// REPEAT 1 - TIME: 3.2134578 s

method {:test} Test3() {
expect 451 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(2, 451);
expect r0 == 2 * 451;
}
method {:test} Test4() {
expect 452 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(452, 452);
expect r0 == 452 * 452;
}
method {:test} Test5() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(2, 2);
expect 2 == 2 * r0 + r1;
}

// REPEAT 2 - TIME: 4.5755104 s

method {:test} Test6() {
expect 453 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(453, 453);
expect r0 == 453 * 453;
}
method {:test} Test7() {
expect 453 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(454, 453);
expect r0 == 454 * 453;
}
method {:test} Test8() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(3, 3);
expect 3 == 3 * r0 + r1;
}

// REPEAT 3 - TIME: 6.1523357 s

method {:test} Test9() {
expect 454 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(455, 454);
expect r0 == 455 * 454;
}
method {:test} Test11() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(4, 4);
expect 4 == 4 * r0 + r1;
}

// REPEAT 4 - TIME: 7.9261877 s

method {:test} Test12() {
expect 455 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(456, 455);
expect r0 == 456 * 455;
}
method {:test} Test14() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(5, 5);
expect 5 == 5 * r0 + r1;
}

// REPEAT 5 - TIME: 9.5636358 s

method {:test} Test15() {
expect 456 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(457, 456);
expect r0 == 457 * 456;
}
method {:test} Test17() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(6, 6);
expect 6 == 6 * r0 + r1;
}

// REPEAT 6 - TIME: 10.8349758 s

method {:test} Test18() {
expect 457 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(458, 457);
expect r0 == 458 * 457;
}
method {:test} Test20() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7, 7);
expect 7 == 7 * r0 + r1;
}

// REPEAT 7 - TIME: 12.2169114 s

method {:test} Test21() {
expect 458 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(459, 458);
expect r0 == 459 * 458;
}
method {:test} Test22() {
expect 460 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(3, 460);
expect r0 == 3 * 460;
}
method {:test} Test23() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(8, 8);
expect 8 == 8 * r0 + r1;
}

// REPEAT 8 - TIME: 13.4524596 s

method {:test} Test24() {
expect 461 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(460, 461);
expect r0 == 460 * 461;
}
method {:test} Test26() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(9, 9);
expect 9 == 9 * r0 + r1;
}

// REPEAT 9 - TIME: 14.7449187 s

method {:test} Test27() {
expect 462 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(461, 462);
expect r0 == 461 * 462;
}
method {:test} Test29() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(10, 10);
expect 10 == 10 * r0 + r1;
}

// REPEAT 10 - TIME: 16.2894207 s
