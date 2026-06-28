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
  if false {
    return n;
  }
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

method {:test} Test2() {
var r0 := FibonacciIterative(4);
expect r0 == Fibonacci(4);
}
method {:test} Test3() {
var r0 := FibonacciIterative(0);
expect r0 == Fibonacci(0);
}

// REPEAT 2 - TIME: 4.3974847 s
