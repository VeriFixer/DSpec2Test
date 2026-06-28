// dafny-synthesis_task_id_3.dfy

method {:testEntry} IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k :: 2 <= k < n && n % k == 0
{
  result := false;
  var i := 2;
  while i >= n / 2
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
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(4);
expect r0 <==> exists k :: 2 <= k < 4 && 4 % k == 0;
}
method {:test} Test1() {
expect 40 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(40);
expect r0 <==> exists k :: 2 <= k < 40 && 40 % k == 0;
}

// REPEAT 1 - TIME: 3.7850432 s

method {:test} Test2() {
expect 42 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(42);
expect r0 <==> exists k :: 2 <= k < 42 && 42 % k == 0;
}
method {:test} Test3() {
expect 41 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(41);
expect r0 <==> exists k :: 2 <= k < 41 && 41 % k == 0;
}

// REPEAT 2 - TIME: 5.3936242 s

method {:test} Test4() {
expect 44 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(44);
expect r0 <==> exists k :: 2 <= k < 44 && 44 % k == 0;
}
method {:test} Test5() {
expect 43 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(43);
expect r0 <==> exists k :: 2 <= k < 43 && 43 % k == 0;
}

// REPEAT 3 - TIME: 6.720796 s

method {:test} Test6() {
expect 46 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(46);
expect r0 <==> exists k :: 2 <= k < 46 && 46 % k == 0;
}
method {:test} Test7() {
expect 45 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(45);
expect r0 <==> exists k :: 2 <= k < 45 && 45 % k == 0;
}

// REPEAT 4 - TIME: 8.0228024 s

method {:test} Test8() {
expect 48 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(48);
expect r0 <==> exists k :: 2 <= k < 48 && 48 % k == 0;
}
method {:test} Test9() {
expect 47 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(47);
expect r0 <==> exists k :: 2 <= k < 47 && 47 % k == 0;
}

// REPEAT 5 - TIME: 9.1331785 s

method {:test} Test10() {
expect 50 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(50);
expect r0 <==> exists k :: 2 <= k < 50 && 50 % k == 0;
}
method {:test} Test11() {
expect 49 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(49);
expect r0 <==> exists k :: 2 <= k < 49 && 49 % k == 0;
}

// REPEAT 6 - TIME: 10.2177349 s

method {:test} Test12() {
expect 52 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(52);
expect r0 <==> exists k :: 2 <= k < 52 && 52 % k == 0;
}
method {:test} Test13() {
expect 51 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(51);
expect r0 <==> exists k :: 2 <= k < 51 && 51 % k == 0;
}

// REPEAT 7 - TIME: 11.5058488 s

method {:test} Test14() {
expect 54 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(54);
expect r0 <==> exists k :: 2 <= k < 54 && 54 % k == 0;
}
method {:test} Test15() {
expect 53 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(53);
expect r0 <==> exists k :: 2 <= k < 53 && 53 % k == 0;
}

// REPEAT 8 - TIME: 12.6504852 s

method {:test} Test16() {
expect 56 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(56);
expect r0 <==> exists k :: 2 <= k < 56 && 56 % k == 0;
}
method {:test} Test17() {
expect 55 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(55);
expect r0 <==> exists k :: 2 <= k < 55 && 55 % k == 0;
}

// REPEAT 9 - TIME: 13.7951808 s

method {:test} Test18() {
expect 58 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(58);
expect r0 <==> exists k :: 2 <= k < 58 && 58 % k == 0;
}
method {:test} Test19() {
expect 57 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(57);
expect r0 <==> exists k :: 2 <= k < 57 && 57 % k == 0;
}

// REPEAT 10 - TIME: 15.0604033 s
