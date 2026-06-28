// dafny-synthesis_task_id_3.dfy

method {:testEntry} IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k :: 2 <= k < n && n % k == 0
{
  result := false;
  var i := 2;
  while i != n / 2
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
expect 5 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(5);
expect r0 <==> exists k :: 2 <= k < 5 && 5 % k == 0;
}
method {:test} Test1() {
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(4);
expect r0 <==> exists k :: 2 <= k < 4 && 4 % k == 0;
}

// REPEAT 1 - TIME: 3.1314767 s

method {:test} Test2() {
expect 7 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(7);
expect r0 <==> exists k :: 2 <= k < 7 && 7 % k == 0;
}
method {:test} Test3() {
expect 6 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(6);
expect r0 <==> exists k :: 2 <= k < 6 && 6 % k == 0;
}

// REPEAT 2 - TIME: 4.1569271 s

method {:test} Test4() {
expect 571 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(571);
expect r0 <==> exists k :: 2 <= k < 571 && 571 % k == 0;
}
method {:test} Test5() {
expect 8 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(8);
expect r0 <==> exists k :: 2 <= k < 8 && 8 % k == 0;
}

// REPEAT 3 - TIME: 5.6206481 s

method {:test} Test6() {
expect 573 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(573);
expect r0 <==> exists k :: 2 <= k < 573 && 573 % k == 0;
}
method {:test} Test7() {
expect 572 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(572);
expect r0 <==> exists k :: 2 <= k < 572 && 572 % k == 0;
}

// REPEAT 4 - TIME: 7.3470823 s

method {:test} Test8() {
expect 575 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(575);
expect r0 <==> exists k :: 2 <= k < 575 && 575 % k == 0;
}
method {:test} Test9() {
expect 574 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(574);
expect r0 <==> exists k :: 2 <= k < 574 && 574 % k == 0;
}

// REPEAT 5 - TIME: 8.9192837 s

method {:test} Test10() {
expect 577 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(577);
expect r0 <==> exists k :: 2 <= k < 577 && 577 % k == 0;
}
method {:test} Test11() {
expect 576 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(576);
expect r0 <==> exists k :: 2 <= k < 576 && 576 % k == 0;
}

// REPEAT 6 - TIME: 10.0583878 s

method {:test} Test12() {
expect 579 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(579);
expect r0 <==> exists k :: 2 <= k < 579 && 579 % k == 0;
}
method {:test} Test13() {
expect 578 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(578);
expect r0 <==> exists k :: 2 <= k < 578 && 578 % k == 0;
}

// REPEAT 7 - TIME: 11.0743327 s

method {:test} Test14() {
expect 581 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(581);
expect r0 <==> exists k :: 2 <= k < 581 && 581 % k == 0;
}
method {:test} Test15() {
expect 580 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(580);
expect r0 <==> exists k :: 2 <= k < 580 && 580 % k == 0;
}

// REPEAT 8 - TIME: 12.099741 s

method {:test} Test16() {
expect 583 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(583);
expect r0 <==> exists k :: 2 <= k < 583 && 583 % k == 0;
}
method {:test} Test17() {
expect 582 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(582);
expect r0 <==> exists k :: 2 <= k < 582 && 582 % k == 0;
}

// REPEAT 9 - TIME: 13.05497 s

method {:test} Test18() {
expect 585 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(585);
expect r0 <==> exists k :: 2 <= k < 585 && 585 % k == 0;
}
method {:test} Test19() {
expect 584 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(584);
expect r0 <==> exists k :: 2 <= k < 584 && 584 % k == 0;
}

// REPEAT 10 - TIME: 14.078825 s
