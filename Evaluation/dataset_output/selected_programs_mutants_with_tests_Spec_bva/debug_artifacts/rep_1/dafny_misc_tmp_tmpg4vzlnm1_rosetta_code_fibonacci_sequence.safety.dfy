// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

// iterative calculation of Fibonacci numbers
method {:testEntry} FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{
  if n < 2 {
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
method {:test} Test1() {
var r0 := FibonacciIterative(100);
expect r0 == Fibonacci(100);
}
method {:test} Test3() {
var r0 := FibonacciIterative(3);
expect r0 == Fibonacci(3);
}
method {:test} Test4() {
var r0 := FibonacciIterative(2441);
expect r0 == Fibonacci(2441);
}

// REPEAT 1 - TIME: 8.0816072 s
