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

// REPEAT 1 - TIME: 3.442182 s

method {:test} Test2() {
var r0 := FibonacciIterative(1);
expect r0 == Fibonacci(1);
}
method {:test} Test3() {
var r0 := FibonacciIterative(2443);
expect r0 == Fibonacci(2443);
}

// REPEAT 2 - TIME: 5.8201313 s

method {:test} Test4() {
var r0 := FibonacciIterative(2444);
expect r0 == Fibonacci(2444);
}

// REPEAT 3 - TIME: 7.7901642 s

method {:test} Test5() {
var r0 := FibonacciIterative(2445);
expect r0 == Fibonacci(2445);
}

// REPEAT 4 - TIME: 9.4992353 s

method {:test} Test6() {
var r0 := FibonacciIterative(2446);
expect r0 == Fibonacci(2446);
}

// REPEAT 5 - TIME: 11.3005162 s

method {:test} Test7() {
var r0 := FibonacciIterative(2447);
expect r0 == Fibonacci(2447);
}

// REPEAT 6 - TIME: 13.1462887 s

method {:test} Test8() {
var r0 := FibonacciIterative(2448);
expect r0 == Fibonacci(2448);
}

// REPEAT 7 - TIME: 15.1396248 s

method {:test} Test9() {
var r0 := FibonacciIterative(2449);
expect r0 == Fibonacci(2449);
}

// REPEAT 8 - TIME: 17.25317 s

method {:test} Test10() {
var r0 := FibonacciIterative(2450);
expect r0 == Fibonacci(2450);
}

// REPEAT 9 - TIME: 19.1799731 s

method {:test} Test11() {
var r0 := FibonacciIterative(2451);
expect r0 == Fibonacci(2451);
}

// REPEAT 10 - TIME: 21.1389695 s
