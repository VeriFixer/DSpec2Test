// dafny-synthesis_task_id_3.dfy

method {:testEntry} IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k :: 2 <= k < n && n % k == 0
{
  result := false;
  var i := 2;
  while i <= n * 2
    invariant 2 <= i
    invariant result <==> exists k :: 2 <= k < i && n % k == 0
  {
    if n % i == 0 {
      result := true;
      break;
    }
    i := i + 1;
  }
}


method {:test} Test0() {
expect 2 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(2);
expect r0 <==> exists k :: 2 <= k < 2 && 2 % k == 0;
}
method {:test} Test1() {
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(4);
expect r0 <==> exists k :: 2 <= k < 4 && 4 % k == 0;
}

// REPEAT 1 - TIME: 10.5786383 s

method {:test} Test2() {
expect 15444 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15444);
expect r0 <==> exists k :: 2 <= k < 15444 && 15444 % k == 0;
}
method {:test} Test3() {
expect 6 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(6);
expect r0 <==> exists k :: 2 <= k < 6 && 6 % k == 0;
}

// REPEAT 2 - TIME: 17.8168185 s

method {:test} Test4() {
expect 15446 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15446);
expect r0 <==> exists k :: 2 <= k < 15446 && 15446 % k == 0;
}

// REPEAT 3 - TIME: 25.0621253 s

method {:test} Test6() {
expect 15448 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15448);
expect r0 <==> exists k :: 2 <= k < 15448 && 15448 % k == 0;
}

// REPEAT 4 - TIME: 33.1805672 s

method {:test} Test8() {
expect 15450 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15450);
expect r0 <==> exists k :: 2 <= k < 15450 && 15450 % k == 0;
}

// REPEAT 5 - TIME: 41.1416092 s

method {:test} Test10() {
expect 15452 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15452);
expect r0 <==> exists k :: 2 <= k < 15452 && 15452 % k == 0;
}

// REPEAT 6 - TIME: 50.089261 s

method {:test} Test12() {
expect 15454 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15454);
expect r0 <==> exists k :: 2 <= k < 15454 && 15454 % k == 0;
}

// REPEAT 7 - TIME: 57.220574 s

method {:test} Test14() {
expect 15455 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15455);
expect r0 <==> exists k :: 2 <= k < 15455 && 15455 % k == 0;
}
method {:test} Test15() {
expect 15456 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15456);
expect r0 <==> exists k :: 2 <= k < 15456 && 15456 % k == 0;
}

// REPEAT 8 - TIME: 65.6551842 s

method {:test} Test16() {
expect 15458 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15458);
expect r0 <==> exists k :: 2 <= k < 15458 && 15458 % k == 0;
}

// REPEAT 9 - TIME: 72.7163762 s

method {:test} Test18() {
expect 15460 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15460);
expect r0 <==> exists k :: 2 <= k < 15460 && 15460 % k == 0;
}

// REPEAT 10 - TIME: 80.4557139 s
