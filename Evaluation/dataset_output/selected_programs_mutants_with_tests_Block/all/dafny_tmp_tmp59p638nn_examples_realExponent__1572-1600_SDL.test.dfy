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
  while i < n
    invariant i <= n
    invariant product == power(i as real, alpha)
  {
    product := product * alpha;
    i := i + 1;
  }
  assert i == n;
  assert product == power(n as real, alpha);
}


method {:test} Test0() {
expect 8366 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8366, 1.0/2.0);
}

// REPEAT 1 - TIME: 3.4344662 s

method {:test} Test1() {
expect 8367 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8367, 3.0/2.0);
}

// REPEAT 2 - TIME: 4.9976508 s

method {:test} Test2() {
expect 8368 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8368, 5.0/2.0);
}

// REPEAT 3 - TIME: 6.4470249 s

method {:test} Test3() {
expect 8369 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8369, 7.0/2.0);
}

// REPEAT 4 - TIME: 8.0216737 s

method {:test} Test4() {
expect 8370 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8370, 9.0/2.0);
}

// REPEAT 5 - TIME: 9.3004569 s

method {:test} Test5() {
expect 8371 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 11.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8371, 11.0/2.0);
}

// REPEAT 6 - TIME: 10.4412962 s

method {:test} Test6() {
expect 8372 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 13.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8372, 13.0/2.0);
}

// REPEAT 7 - TIME: 11.5110224 s

method {:test} Test7() {
expect 8373 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 15.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8373, 15.0/2.0);
}

// REPEAT 8 - TIME: 12.4549791 s

method {:test} Test8() {
expect 8374 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 17.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8374, 17.0/2.0);
}

// REPEAT 9 - TIME: 13.3753555 s

method {:test} Test9() {
expect 8375 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 19.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(8375, 19.0/2.0);
}

// REPEAT 10 - TIME: 14.2584758 s
