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
  return n;
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
var r0 := FibonacciIterative(1);
expect r0 == Fibonacci(1);
}

// REPEAT 1 - TIME: 3.0596398 s

method {:test} Test1() {
var r0 := FibonacciIterative(2);
expect r0 == Fibonacci(2);
}

// REPEAT 2 - TIME: 4.253807 s

method {:test} Test2() {
var r0 := FibonacciIterative(3);
expect r0 == Fibonacci(3);
}

// REPEAT 3 - TIME: 5.3490655 s

method {:test} Test3() {
var r0 := FibonacciIterative(2441);
expect r0 == Fibonacci(2441);
}

// REPEAT 4 - TIME: 6.4195735 s

method {:test} Test4() {
var r0 := FibonacciIterative(2442);
expect r0 == Fibonacci(2442);
}

// REPEAT 5 - TIME: 7.3100587 s

method {:test} Test5() {
var r0 := FibonacciIterative(2443);
expect r0 == Fibonacci(2443);
}

// REPEAT 6 - TIME: 8.1351899 s

method {:test} Test6() {
var r0 := FibonacciIterative(2444);
expect r0 == Fibonacci(2444);
}

// REPEAT 7 - TIME: 8.9923317 s

method {:test} Test7() {
var r0 := FibonacciIterative(2445);
expect r0 == Fibonacci(2445);
}

// REPEAT 8 - TIME: 9.7307123 s

method {:test} Test8() {
var r0 := FibonacciIterative(2446);
expect r0 == Fibonacci(2446);
}

// REPEAT 9 - TIME: 10.469714 s

method {:test} Test9() {
var r0 := FibonacciIterative(2447);
expect r0 == Fibonacci(2447);
}

// REPEAT 10 - TIME: 11.1953861 s
