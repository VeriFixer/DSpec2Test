// dafny-synthesis_task_id_3.dfy

method {:testEntry} IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k :: 2 <= k < n && n % k == 0
{
  result := false;
  var i := 2;
  while i < n / 2
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

// REPEAT 1 - TIME: 9.0046296 s

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

// REPEAT 2 - TIME: 14.8245376 s

method {:test} Test4() {
expect 15446 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15446);
expect r0 <==> exists k :: 2 <= k < 15446 && 15446 % k == 0;
}

// REPEAT 3 - TIME: 20.3188324 s

method {:test} Test6() {
expect 15448 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15448);
expect r0 <==> exists k :: 2 <= k < 15448 && 15448 % k == 0;
}

// REPEAT 4 - TIME: 26.713924 s

method {:test} Test8() {
expect 15450 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15450);
expect r0 <==> exists k :: 2 <= k < 15450 && 15450 % k == 0;
}

// REPEAT 5 - TIME: 33.2636313 s

method {:test} Test10() {
expect 15452 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15452);
expect r0 <==> exists k :: 2 <= k < 15452 && 15452 % k == 0;
}

// REPEAT 6 - TIME: 39.4129734 s

method {:test} Test12() {
expect 15454 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15454);
expect r0 <==> exists k :: 2 <= k < 15454 && 15454 % k == 0;
}

// REPEAT 7 - TIME: 46.9261421 s

method {:test} Test14() {
expect 15456 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15456);
expect r0 <==> exists k :: 2 <= k < 15456 && 15456 % k == 0;
}

// REPEAT 8 - TIME: 53.2473739 s

method {:test} Test16() {
expect 15457 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15457);
expect r0 <==> exists k :: 2 <= k < 15457 && 15457 % k == 0;
}
method {:test} Test17() {
expect 15458 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15458);
expect r0 <==> exists k :: 2 <= k < 15458 && 15458 % k == 0;
}

// REPEAT 9 - TIME: 60.6817328 s

method {:test} Test18() {
expect 15459 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15459);
expect r0 <==> exists k :: 2 <= k < 15459 && 15459 % k == 0;
}
method {:test} Test19() {
expect 15460 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15460);
expect r0 <==> exists k :: 2 <= k < 15460 && 15460 % k == 0;
}

// REPEAT 10 - TIME: 67.9779176 s
