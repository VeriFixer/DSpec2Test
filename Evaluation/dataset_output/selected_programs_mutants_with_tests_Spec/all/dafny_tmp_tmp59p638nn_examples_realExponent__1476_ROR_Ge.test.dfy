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
  while i >= n
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

// REPEAT 1 - TIME: 3.6770229 s

method {:test} Test1() {
expect 1238 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1238, 3.0/2.0);
}

// REPEAT 2 - TIME: 4.7910532 s

method {:test} Test2() {
expect 1239 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1239, 5.0/2.0);
}

// REPEAT 3 - TIME: 6.0411145 s

method {:test} Test3() {
expect 1240 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1240, 7.0/2.0);
}

// REPEAT 4 - TIME: 7.2149088 s

method {:test} Test4() {
expect 1241 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1241, 9.0/2.0);
}

// REPEAT 5 - TIME: 8.5748133 s

method {:test} Test5() {
expect 1242 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 11.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1242, 11.0/2.0);
}

// REPEAT 6 - TIME: 9.6868311 s

method {:test} Test6() {
expect 1243 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 13.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1243, 13.0/2.0);
}

// REPEAT 7 - TIME: 10.8538 s

method {:test} Test7() {
expect 1244 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 15.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1244, 15.0/2.0);
}

// REPEAT 8 - TIME: 11.7814064 s

method {:test} Test8() {
expect 1245 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 17.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1245, 17.0/2.0);
}

// REPEAT 9 - TIME: 12.6027365 s

method {:test} Test9() {
expect 1246 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 19.0/2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := pow(1246, 19.0/2.0);
}

// REPEAT 10 - TIME: 13.3441058 s
