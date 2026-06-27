// dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_fibonacci.dfy

function fib(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}

method {:testEntry} ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  if n == 0 {
    f := 0;
  } else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
    while i < n
      invariant i <= n
      invariant f_1 == fib(i - 1)
      invariant f == fib(i)
      decreases n - i
    {
      f_2 := f_1;
      f_1 := f;
      f := f_1 + f_2;
      i := i + 1;
    }
  }
}


method {:test} Test0() {
var r0 := ComputeFib(1);
expect r0 == fib(1);
}

// REPEAT 1 - TIME: 2.6726947 s

method {:test} Test1() {
var r0 := ComputeFib(2);
expect r0 == fib(2);
}

// REPEAT 2 - TIME: 3.5158454 s

method {:test} Test2() {
var r0 := ComputeFib(3);
expect r0 == fib(3);
}

// REPEAT 3 - TIME: 4.4648784 s

method {:test} Test3() {
var r0 := ComputeFib(2441);
expect r0 == fib(2441);
}

// REPEAT 4 - TIME: 5.4238939 s

method {:test} Test4() {
var r0 := ComputeFib(2442);
expect r0 == fib(2442);
}

// REPEAT 5 - TIME: 6.3622996 s

method {:test} Test5() {
var r0 := ComputeFib(2443);
expect r0 == fib(2443);
}

// REPEAT 6 - TIME: 7.2791019 s

method {:test} Test6() {
var r0 := ComputeFib(2444);
expect r0 == fib(2444);
}

// REPEAT 7 - TIME: 8.0230009 s

method {:test} Test7() {
var r0 := ComputeFib(2445);
expect r0 == fib(2445);
}

// REPEAT 8 - TIME: 8.7659966 s

method {:test} Test8() {
var r0 := ComputeFib(2446);
expect r0 == fib(2446);
}

// REPEAT 9 - TIME: 9.5449642 s

method {:test} Test9() {
var r0 := ComputeFib(2447);
expect r0 == fib(2447);
}

// REPEAT 10 - TIME: 10.071727 s
