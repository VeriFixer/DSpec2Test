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
  while true
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
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1796, 1);
expect r0 == 1796 * 1;
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(0, 1);
expect 0 == 1 * r0 + r1;
}

// REPEAT 1 - TIME: 3.5839477 s

method {:test} Test2() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1797, 2);
expect r0 == 1797 * 2;
}
method {:test} Test3() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(1, 2);
expect 1 == 2 * r0 + r1;
}

// REPEAT 2 - TIME: 5.0338449 s

method {:test} Test4() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1798, 3);
expect r0 == 1798 * 3;
}
method {:test} Test5() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8858 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(2, 8858);
expect 2 == 8858 * r0 + r1;
}

// REPEAT 3 - TIME: 6.5217279 s

method {:test} Test6() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1799, 4);
expect r0 == 1799 * 4;
}
method {:test} Test7() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8859 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(3, 8859);
expect 3 == 8859 * r0 + r1;
}

// REPEAT 4 - TIME: 8.088776 s

method {:test} Test8() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1800, 5);
expect r0 == 1800 * 5;
}
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8860 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(4, 8860);
expect 4 == 8860 * r0 + r1;
}

// REPEAT 5 - TIME: 9.48495 s

method {:test} Test10() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1801, 6);
expect r0 == 1801 * 6;
}
method {:test} Test11() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8861 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(5, 8861);
expect 5 == 8861 * r0 + r1;
}

// REPEAT 6 - TIME: 10.6349993 s

method {:test} Test12() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1802, 7);
expect r0 == 1802 * 7;
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8862 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(6, 8862);
expect 6 == 8862 * r0 + r1;
}

// REPEAT 7 - TIME: 11.5426717 s

method {:test} Test14() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1803, 8);
expect r0 == 1803 * 8;
}
method {:test} Test15() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8863 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7, 8863);
expect 7 == 8863 * r0 + r1;
}

// REPEAT 8 - TIME: 12.6256047 s

method {:test} Test16() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1804, 9);
expect r0 == 1804 * 9;
}
method {:test} Test17() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8864 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(8, 8864);
expect 8 == 8864 * r0 + r1;
}

// REPEAT 9 - TIME: 13.4233621 s

method {:test} Test18() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1805, 10);
expect r0 == 1805 * 10;
}
method {:test} Test19() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8865 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(9, 8865);
expect 9 == 8865 * r0 + r1;
}

// REPEAT 10 - TIME: 14.3660117 s
