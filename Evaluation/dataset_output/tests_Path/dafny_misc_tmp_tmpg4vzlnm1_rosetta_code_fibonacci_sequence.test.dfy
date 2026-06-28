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
var r0 := FibonacciIterative(0);
expect r0 == Fibonacci(0);
}
method {:test} Test1() {
var r0 := FibonacciIterative(2442);
expect r0 == Fibonacci(2442);
}

// REPEAT 1 - TIME: 4.7176293 s

method {:test} Test2() {
var r0 := FibonacciIterative(1);
expect r0 == Fibonacci(1);
}
method {:test} Test3() {
var r0 := FibonacciIterative(2443);
expect r0 == Fibonacci(2443);
}

// REPEAT 2 - TIME: 7.6879717 s

method {:test} Test4() {
var r0 := FibonacciIterative(2444);
expect r0 == Fibonacci(2444);
}

// REPEAT 3 - TIME: 9.983972 s

method {:test} Test5() {
var r0 := FibonacciIterative(2445);
expect r0 == Fibonacci(2445);
}

// REPEAT 4 - TIME: 12.273471 s

method {:test} Test6() {
var r0 := FibonacciIterative(2446);
expect r0 == Fibonacci(2446);
}

// REPEAT 5 - TIME: 14.8360196 s

method {:test} Test7() {
var r0 := FibonacciIterative(2447);
expect r0 == Fibonacci(2447);
}

// REPEAT 6 - TIME: 17.372092 s

method {:test} Test8() {
var r0 := FibonacciIterative(2448);
expect r0 == Fibonacci(2448);
}

// REPEAT 7 - TIME: 20.2348128 s

method {:test} Test9() {
var r0 := FibonacciIterative(2449);
expect r0 == Fibonacci(2449);
}

// REPEAT 8 - TIME: 22.9595177 s

method {:test} Test10() {
var r0 := FibonacciIterative(2450);
expect r0 == Fibonacci(2450);
}

// REPEAT 9 - TIME: 26.3993325 s

method {:test} Test11() {
var r0 := FibonacciIterative(2451);
expect r0 == Fibonacci(2451);
}

// REPEAT 10 - TIME: 29.0478231 s
