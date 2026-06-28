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
  while bb > 0
    invariant 0 <= bb <= b
    invariant r + aa * bb == a * b
    decreases bb
  {
    if bb % 2 < 0 {
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
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(0, 1);
expect r0 == 0 * 1;
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(0, 1);
expect 0 == 1 * r0 + r1;
}

// REPEAT 1 - TIME: 10.2585769 s

method {:test} Test2() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1, 2);
expect r0 == 1 * 2;
}
method {:test} Test3() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(1, 2);
expect 1 == 2 * r0 + r1;
}

// REPEAT 2 - TIME: 17.7994194 s

method {:test} Test4() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(2, 3);
expect r0 == 2 * 3;
}
method {:test} Test5() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(2, 3);
expect 2 == 3 * r0 + r1;
}

// REPEAT 3 - TIME: 26.2751518 s

method {:test} Test6() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(3, 4);
expect r0 == 3 * 4;
}
method {:test} Test7() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(3, 4);
expect 3 == 4 * r0 + r1;
}

// REPEAT 4 - TIME: 34.0864296 s

method {:test} Test8() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(4, 5);
expect r0 == 4 * 5;
}
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(4, 5);
expect 4 == 5 * r0 + r1;
}

// REPEAT 5 - TIME: 41.6925122 s

method {:test} Test10() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(5, 6);
expect r0 == 5 * 6;
}
method {:test} Test11() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(5, 6);
expect 5 == 6 * r0 + r1;
}

// REPEAT 6 - TIME: 48.9483159 s

method {:test} Test12() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(6, 7);
expect r0 == 6 * 7;
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(6, 7);
expect 6 == 7 * r0 + r1;
}

// REPEAT 7 - TIME: 56.81619 s

method {:test} Test14() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7, 8);
expect r0 == 7 * 8;
}
method {:test} Test15() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7, 8);
expect 7 == 8 * r0 + r1;
}

// REPEAT 8 - TIME: 66.2852557 s

method {:test} Test16() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(8, 9);
expect r0 == 8 * 9;
}
method {:test} Test17() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(8, 9);
expect 8 == 9 * r0 + r1;
}

// REPEAT 9 - TIME: 75.2238991 s

method {:test} Test18() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(9, 10);
expect r0 == 9 * 10;
}
method {:test} Test19() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(9, 10);
expect 9 == 10 * r0 + r1;
}

// REPEAT 10 - TIME: 85.3170327 s
