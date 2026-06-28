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
  if n != 2 {
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

method {:test} Test0() {
var r0 := FibonacciIterative(1);
expect r0 == Fibonacci(1);
}

// REPEAT 1 - TIME: 3.0596398 s
