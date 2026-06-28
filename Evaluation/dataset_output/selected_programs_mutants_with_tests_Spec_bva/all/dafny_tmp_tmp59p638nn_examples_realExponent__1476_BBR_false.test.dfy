// dafny_tmp_tmp59p638nn_examples_realExponent.dfy

ghost function power(n: real, alpha: real): real
  requires n > 0.0 && alpha > 0.0
  ensures power(n, alpha) > 0.0

ghost function log(n: real, alpha: real): real
  requires n > 0.0 && alpha > 0.0
  ensures log(n, alpha) > 0.0

lemma consistency(n: real, alpha: real)
  requires n > 0.0 && alpha > 0.0
  ensures log(power(n, alpha), alpha) == n
  ensures power(log(n, alpha), alpha) == n

lemma logarithmSum(n: real, alpha: real, x: real, y: real)
  requires n > 0.0 && alpha > 0.0
  requires x > 0.0
  requires n == x * y
  ensures log(n, alpha) == log(x, alpha) + log(y, alpha)

lemma powerLemma(n: real, alpha: real)
  requires n > 0.0 && alpha > 0.0
  ensures power(n, alpha) * alpha == power(n + 1.0, alpha)

lemma power1(alpha: real)
  requires alpha > 0.0
  ensures power(1.0, alpha) == alpha

lemma test()
{
  var pow3 := power(3.0, 4.0);
  consistency(3.0, 4.0);
  assert log(pow3, 4.0) == 3.0;
  var log6 := log(6.0, 8.0);
  logarithmSum(6.0, 8.0, 2.0, 3.0);
  assert log6 == log(2.0, 8.0) + log(3.0, 8.0);
}

lemma test2()
{
  var pow3 := power(3.0, 4.0);
  var power4 := power(4.0, 4.0);
  powerLemma(3.0, 4.0);
  assert pow3 * 4.0 == power4;
}

method {:testEntry} pow(n: nat, alpha: real) returns (product: real)
  requires n > 0
  requires alpha > 0.0
  ensures product == power(n as real, alpha)
{
  product := alpha;
  var i: nat := 1;
  power1(alpha);
  assert product == power(1.0, alpha);
  while false
    invariant i <= n
    invariant product == power(i as real, alpha)
  {
    powerLemma(i as real, alpha);
    product := product * alpha;
    i := i + 1;
  }
  assert i == n;
  assert product == power(n as real, alpha);
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1, 1.0/2.0);
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(100, 1.0);
}
method {:test} Test3() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0/10000.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1, 1.0/10000.0);
}
method {:test} Test4() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1, 100.0);
}

// REPEAT 1 - TIME: 10.4604203 s

method {:test} Test9() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 201.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(101, 201.0/2.0);
}

// REPEAT 2 - TIME: 11.5417457 s

method {:test} Test10() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 203.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(102, 203.0/2.0);
}

// REPEAT 3 - TIME: 12.7003339 s

method {:test} Test11() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 205.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(103, 205.0/2.0);
}

// REPEAT 4 - TIME: 13.9372815 s

method {:test} Test12() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 207.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(104, 207.0/2.0);
}

// REPEAT 5 - TIME: 15.1688965 s

method {:test} Test13() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 209.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(105, 209.0/2.0);
}

// REPEAT 6 - TIME: 16.2824327 s

method {:test} Test14() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 211.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(106, 211.0/2.0);
}

// REPEAT 7 - TIME: 17.1129507 s

method {:test} Test15() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 213.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(107, 213.0/2.0);
}

// REPEAT 8 - TIME: 17.9916762 s

method {:test} Test16() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 215.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(108, 215.0/2.0);
}

// REPEAT 9 - TIME: 18.8999044 s

method {:test} Test17() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 217.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(109, 217.0/2.0);
}

// REPEAT 10 - TIME: 19.6372337 s
