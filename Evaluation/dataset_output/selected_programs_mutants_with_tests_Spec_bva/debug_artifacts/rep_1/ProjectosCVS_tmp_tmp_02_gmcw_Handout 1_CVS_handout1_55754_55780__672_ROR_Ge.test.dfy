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
