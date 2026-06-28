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
  while f != i
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

method {:test} Test18() {
expect 1 < 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(103);
expect r0 == IsPrime(103);
}
method {:test} Test19() {
expect 1 < 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := test_prime(104);
expect r0 == IsPrime(104);
}

// REPEAT 3 - TIME: 16.9982998 s
