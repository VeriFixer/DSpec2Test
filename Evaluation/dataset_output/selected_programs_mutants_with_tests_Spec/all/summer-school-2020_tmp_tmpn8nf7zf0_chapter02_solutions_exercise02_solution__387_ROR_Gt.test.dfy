// summer-school-2020_tmp_tmpn8nf7zf0_chapter02_solutions_exercise02_solution.dfy

predicate divides(f: nat, i: nat)
  requires 1 <= f
{
  i % f == 0
}

predicate IsPrime(i: nat)
{
  1 < i &&
  forall f :: 
    1 < f < i ==>
      !divides(f, i)
}

method {:testEntry} test_prime(i: nat) returns (result: bool)
  requires 1 < i
  ensures result == IsPrime(i)
{
  var f := 2;
  while f > i
    invariant forall g :: 1 < g < f ==> !divides(g, i)
  {
    if i % f == 0 {
      assert divides(f, i);
      return false;
    }
    f := f + 1;
  }
  return true;
}

method {:testEntry} Main()
{
  var a := test_prime(3);
  assert a;
  var b := test_prime(4);
  assert divides(2, 4);
  assert !b;
  var c := test_prime(5);
  assert c;
}


method {:test} Test0() {
expect 1 < 40, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(40);
expect r0 == IsPrime(40);
}
method {:test} Test1() {
expect 1 < 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(4);
expect r0 == IsPrime(4);
}
method {:test} Test2() {
Main();
}

// REPEAT 1 - TIME: 4.4763914 s

method {:test} Test3() {
expect 1 < 41, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(41);
expect r0 == IsPrime(41);
}
method {:test} Test4() {
expect 1 < 42, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(42);
expect r0 == IsPrime(42);
}

// REPEAT 2 - TIME: 6.1857197 s

method {:test} Test5() {
expect 1 < 43, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(43);
expect r0 == IsPrime(43);
}
method {:test} Test6() {
expect 1 < 44, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(44);
expect r0 == IsPrime(44);
}

// REPEAT 3 - TIME: 7.8699533 s

method {:test} Test7() {
expect 1 < 45, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(45);
expect r0 == IsPrime(45);
}
method {:test} Test8() {
expect 1 < 46, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(46);
expect r0 == IsPrime(46);
}

// REPEAT 4 - TIME: 9.2570479 s

method {:test} Test9() {
expect 1 < 47, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(47);
expect r0 == IsPrime(47);
}
method {:test} Test10() {
expect 1 < 48, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(48);
expect r0 == IsPrime(48);
}

// REPEAT 5 - TIME: 10.2663577 s

method {:test} Test11() {
expect 1 < 49, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(49);
expect r0 == IsPrime(49);
}
method {:test} Test12() {
expect 1 < 50, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(50);
expect r0 == IsPrime(50);
}

// REPEAT 6 - TIME: 11.1342617 s

method {:test} Test13() {
expect 1 < 51, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(51);
expect r0 == IsPrime(51);
}
method {:test} Test14() {
expect 1 < 52, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(52);
expect r0 == IsPrime(52);
}

// REPEAT 7 - TIME: 12.0171572 s

method {:test} Test15() {
expect 1 < 53, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(53);
expect r0 == IsPrime(53);
}
method {:test} Test16() {
expect 1 < 54, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(54);
expect r0 == IsPrime(54);
}

// REPEAT 8 - TIME: 13.1717144 s

method {:test} Test17() {
expect 1 < 55, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(55);
expect r0 == IsPrime(55);
}
method {:test} Test18() {
expect 1 < 56, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(56);
expect r0 == IsPrime(56);
}

// REPEAT 9 - TIME: 14.2890177 s

method {:test} Test19() {
expect 1 < 57, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(57);
expect r0 == IsPrime(57);
}
method {:test} Test20() {
expect 1 < 58, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(58);
expect r0 == IsPrime(58);
}

// REPEAT 10 - TIME: 15.3752709 s
