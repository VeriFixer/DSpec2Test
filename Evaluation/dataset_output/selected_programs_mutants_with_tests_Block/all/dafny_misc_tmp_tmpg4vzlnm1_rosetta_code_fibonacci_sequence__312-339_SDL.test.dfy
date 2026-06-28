// dafny_misc_tmp_tmpg4vzlnm1_rosetta_code_fibonacci_sequence.dfy

function Fibonacci(n: nat): nat
{
  match n {
    case 0 =>
      0
    case 1 =>
      1
    case _ /* _v0 */ =>
      Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

method {:testEntry} FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{
  var prev := 1;
  f := 1;
  var i := 2;
  while i < n
    invariant i <= n
    invariant prev == Fibonacci(i - 1)
    invariant f == Fibonacci(i)
  {
    prev, f := f, f + prev;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := FibonacciIterative(3);
expect r0 == Fibonacci(3);
}
method {:test} Test1() {
var r0 := FibonacciIterative(1);
expect r0 == Fibonacci(1);
}

// REPEAT 1 - TIME: 3.1033895 s

method {:test} Test2() {
var r0 := FibonacciIterative(4);
expect r0 == Fibonacci(4);
}
method {:test} Test3() {
var r0 := FibonacciIterative(0);
expect r0 == Fibonacci(0);
}

// REPEAT 2 - TIME: 4.3974847 s

method {:test} Test4() {
var r0 := FibonacciIterative(5);
expect r0 == Fibonacci(5);
}

// REPEAT 3 - TIME: 5.7879184 s

method {:test} Test6() {
var r0 := FibonacciIterative(6);
expect r0 == Fibonacci(6);
}

// REPEAT 4 - TIME: 7.2615772 s

method {:test} Test8() {
var r0 := FibonacciIterative(7);
expect r0 == Fibonacci(7);
}

// REPEAT 5 - TIME: 8.5021622 s

method {:test} Test10() {
var r0 := FibonacciIterative(8);
expect r0 == Fibonacci(8);
}

// REPEAT 6 - TIME: 9.8907231 s

method {:test} Test12() {
var r0 := FibonacciIterative(9);
expect r0 == Fibonacci(9);
}

// REPEAT 7 - TIME: 11.080295 s

method {:test} Test14() {
var r0 := FibonacciIterative(10);
expect r0 == Fibonacci(10);
}

// REPEAT 8 - TIME: 12.1356243 s

method {:test} Test16() {
var r0 := FibonacciIterative(11);
expect r0 == Fibonacci(11);
}

// REPEAT 9 - TIME: 13.0086061 s

method {:test} Test18() {
var r0 := FibonacciIterative(12);
expect r0 == Fibonacci(12);
}

// REPEAT 10 - TIME: 13.8259819 s
