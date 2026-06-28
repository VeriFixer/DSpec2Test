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
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1796, 1);
expect r0 == 1796 * 1;
}
method {:test} Test1() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(-100, 1);
expect r0 == -100 * 1;
}
method {:test} Test2() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(100, 1);
expect r0 == 100 * 1;
}
method {:test} Test3() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7719, 1);
expect r0 == 7719 * 1;
}
method {:test} Test4() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(38, 100);
expect r0 == 38 * 100;
}
method {:test} Test7() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(1, 100);
expect r0 == 1 * 100;
}
method {:test} Test10() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(0, 1);
expect 0 == 1 * r0 + r1;
}
method {:test} Test12() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(100, 1);
expect 100 == 1 * r0 + r1;
}
method {:test} Test13() {
expect 7719 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7719, 1);
expect 7719 == 1 * r0 + r1;
}
method {:test} Test14() {
expect 3800 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(3800, 100);
expect 3800 == 100 * r0 + r1;
}

// REPEAT 1 - TIME: 16.136029 s

method {:test} Test23() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7720, 101);
expect r0 == 7720 * 101;
}
method {:test} Test24() {
expect 7720 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7720, 101);
expect 7720 == 101 * r0 + r1;
}

// REPEAT 2 - TIME: 17.6303264 s

method {:test} Test25() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7721, 102);
expect r0 == 7721 * 102;
}
method {:test} Test26() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7721, 102);
expect 7721 == 102 * r0 + r1;
}

// REPEAT 3 - TIME: 18.9874307 s

method {:test} Test27() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7722, 103);
expect r0 == 7722 * 103;
}
method {:test} Test28() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7722, 103);
expect 7722 == 103 * r0 + r1;
}

// REPEAT 4 - TIME: 20.2306841 s

method {:test} Test29() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7723, 104);
expect r0 == 7723 * 104;
}
method {:test} Test30() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7723, 104);
expect 7723 == 104 * r0 + r1;
}

// REPEAT 5 - TIME: 21.5698357 s

method {:test} Test31() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7724, 105);
expect r0 == 7724 * 105;
}
method {:test} Test32() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7724, 105);
expect 7724 == 105 * r0 + r1;
}

// REPEAT 6 - TIME: 23.0325824 s

method {:test} Test33() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7725, 106);
expect r0 == 7725 * 106;
}
method {:test} Test34() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7725, 106);
expect 7725 == 106 * r0 + r1;
}

// REPEAT 7 - TIME: 24.2859215 s

method {:test} Test35() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7726, 107);
expect r0 == 7726 * 107;
}
method {:test} Test36() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7726, 107);
expect 7726 == 107 * r0 + r1;
}

// REPEAT 8 - TIME: 25.4687578 s

method {:test} Test37() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7727, 108);
expect r0 == 7727 * 108;
}
method {:test} Test38() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7727, 108);
expect 7727 == 108 * r0 + r1;
}

// REPEAT 9 - TIME: 26.8228554 s

method {:test} Test39() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := peasantMult(7728, 109);
expect r0 == 7728 * 109;
}
method {:test} Test40() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := euclidianDiv(7728, 109);
expect 7728 == 109 * r0 + r1;
}

// REPEAT 10 - TIME: 28.0659588 s
