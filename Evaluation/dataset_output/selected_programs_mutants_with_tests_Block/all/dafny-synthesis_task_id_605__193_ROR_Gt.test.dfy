// dafny-synthesis_task_id_605.dfy

method {:testEntry} IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall k :: 2 <= k < n ==> n % k != 0
{
  result := true;
  var i := 2;
  while i > n / 2
    invariant 2 <= i
    invariant result <==> forall k :: 2 <= k < i ==> n % k != 0
  {
    if n % i == 0 {
      result := false;
      break;
    }
    i := i + 1;
  }
}


method {:test} Test0() {
expect 5 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(5);
expect r0 <==> forall k :: 2 <= k < 5 ==> 5 % k != 0;
}
method {:test} Test1() {
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(4);
expect r0 <==> forall k :: 2 <= k < 4 ==> 4 % k != 0;
}

// REPEAT 1 - TIME: 2.9955555 s

method {:test} Test2() {
expect 7 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(7);
expect r0 <==> forall k :: 2 <= k < 7 ==> 7 % k != 0;
}
method {:test} Test3() {
expect 6 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(6);
expect r0 <==> forall k :: 2 <= k < 6 ==> 6 % k != 0;
}

// REPEAT 2 - TIME: 4.0158033 s

method {:test} Test4() {
expect 2293 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2293);
expect r0 <==> forall k :: 2 <= k < 2293 ==> 2293 % k != 0;
}
method {:test} Test5() {
expect 8 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(8);
expect r0 <==> forall k :: 2 <= k < 8 ==> 8 % k != 0;
}

// REPEAT 3 - TIME: 5.0691196 s

method {:test} Test6() {
expect 2295 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2295);
expect r0 <==> forall k :: 2 <= k < 2295 ==> 2295 % k != 0;
}
method {:test} Test7() {
expect 2294 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2294);
expect r0 <==> forall k :: 2 <= k < 2294 ==> 2294 % k != 0;
}

// REPEAT 4 - TIME: 6.4102274 s

method {:test} Test8() {
expect 2297 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2297);
expect r0 <==> forall k :: 2 <= k < 2297 ==> 2297 % k != 0;
}
method {:test} Test9() {
expect 2296 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2296);
expect r0 <==> forall k :: 2 <= k < 2296 ==> 2296 % k != 0;
}

// REPEAT 5 - TIME: 7.8068477 s

method {:test} Test10() {
expect 2299 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2299);
expect r0 <==> forall k :: 2 <= k < 2299 ==> 2299 % k != 0;
}
method {:test} Test11() {
expect 2298 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2298);
expect r0 <==> forall k :: 2 <= k < 2298 ==> 2298 % k != 0;
}

// REPEAT 6 - TIME: 9.1681744 s

method {:test} Test12() {
expect 2301 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2301);
expect r0 <==> forall k :: 2 <= k < 2301 ==> 2301 % k != 0;
}
method {:test} Test13() {
expect 2300 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2300);
expect r0 <==> forall k :: 2 <= k < 2300 ==> 2300 % k != 0;
}

// REPEAT 7 - TIME: 10.4173337 s

method {:test} Test14() {
expect 2303 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2303);
expect r0 <==> forall k :: 2 <= k < 2303 ==> 2303 % k != 0;
}
method {:test} Test15() {
expect 2302 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2302);
expect r0 <==> forall k :: 2 <= k < 2302 ==> 2302 % k != 0;
}

// REPEAT 8 - TIME: 11.514101 s

method {:test} Test16() {
expect 2305 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2305);
expect r0 <==> forall k :: 2 <= k < 2305 ==> 2305 % k != 0;
}
method {:test} Test17() {
expect 2304 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2304);
expect r0 <==> forall k :: 2 <= k < 2304 ==> 2304 % k != 0;
}

// REPEAT 9 - TIME: 12.5409437 s

method {:test} Test18() {
expect 2307 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2307);
expect r0 <==> forall k :: 2 <= k < 2307 ==> 2307 % k != 0;
}
method {:test} Test19() {
expect 2306 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2306);
expect r0 <==> forall k :: 2 <= k < 2306 ==> 2306 % k != 0;
}

// REPEAT 10 - TIME: 13.5486631 s
