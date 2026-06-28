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
  if false {
    f := 0;
  } else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
    f := 1;
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
var r0 := ComputeFib(2);
expect r0 == fib(2);
}
method {:test} Test1() {
var r0 := ComputeFib(0);
expect r0 == fib(0);
}

// REPEAT 1 - TIME: 2.6749671 s

method {:test} Test2() {
var r0 := ComputeFib(3);
expect r0 == fib(3);
}

// REPEAT 2 - TIME: 3.8498191 s

method {:test} Test4() {
var r0 := ComputeFib(4);
expect r0 == fib(4);
}

// REPEAT 3 - TIME: 5.0434815 s

method {:test} Test6() {
var r0 := ComputeFib(5);
expect r0 == fib(5);
}

// REPEAT 4 - TIME: 6.2374077 s

method {:test} Test8() {
var r0 := ComputeFib(6);
expect r0 == fib(6);
}

// REPEAT 5 - TIME: 7.3904168 s

method {:test} Test10() {
var r0 := ComputeFib(7);
expect r0 == fib(7);
}

// REPEAT 6 - TIME: 8.3932097 s

method {:test} Test12() {
var r0 := ComputeFib(8);
expect r0 == fib(8);
}

// REPEAT 7 - TIME: 9.1302323 s

method {:test} Test14() {
var r0 := ComputeFib(9);
expect r0 == fib(9);
}

// REPEAT 8 - TIME: 9.9549844 s

method {:test} Test16() {
var r0 := ComputeFib(10);
expect r0 == fib(10);
}

// REPEAT 9 - TIME: 10.7163288 s

method {:test} Test18() {
var r0 := ComputeFib(11);
expect r0 == fib(11);
}

// REPEAT 10 - TIME: 11.5802265 s
