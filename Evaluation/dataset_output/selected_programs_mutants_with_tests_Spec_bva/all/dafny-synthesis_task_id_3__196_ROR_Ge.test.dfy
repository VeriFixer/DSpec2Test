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
expect 100 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(100);
expect r0 <==> exists k :: 2 <= k < 100 && 100 % k == 0;
}
method {:test} Test6() {
expect 40 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(40);
expect r0 <==> exists k :: 2 <= k < 40 && 40 % k == 0;
}
method {:test} Test7() {
expect 2 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(2);
expect r0 <==> exists k :: 2 <= k < 2 && 2 % k == 0;
}

// REPEAT 1 - TIME: 12.2332537 s

method {:test} Test13() {
expect 102 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(102);
expect r0 <==> exists k :: 2 <= k < 102 && 102 % k == 0;
}
method {:test} Test14() {
expect 101 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(101);
expect r0 <==> exists k :: 2 <= k < 101 && 101 % k == 0;
}

// REPEAT 2 - TIME: 13.5620895 s

method {:test} Test15() {
expect 104 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(104);
expect r0 <==> exists k :: 2 <= k < 104 && 104 % k == 0;
}
method {:test} Test16() {
expect 103 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(103);
expect r0 <==> exists k :: 2 <= k < 103 && 103 % k == 0;
}

// REPEAT 3 - TIME: 14.7635243 s

method {:test} Test17() {
expect 106 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(106);
expect r0 <==> exists k :: 2 <= k < 106 && 106 % k == 0;
}
method {:test} Test18() {
expect 105 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(105);
expect r0 <==> exists k :: 2 <= k < 105 && 105 % k == 0;
}

// REPEAT 4 - TIME: 15.9999342 s

method {:test} Test19() {
expect 108 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(108);
expect r0 <==> exists k :: 2 <= k < 108 && 108 % k == 0;
}
method {:test} Test20() {
expect 107 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(107);
expect r0 <==> exists k :: 2 <= k < 107 && 107 % k == 0;
}

// REPEAT 5 - TIME: 17.3048425 s

method {:test} Test21() {
expect 110 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(110);
expect r0 <==> exists k :: 2 <= k < 110 && 110 % k == 0;
}
method {:test} Test22() {
expect 109 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(109);
expect r0 <==> exists k :: 2 <= k < 109 && 109 % k == 0;
}

// REPEAT 6 - TIME: 18.5917253 s

method {:test} Test23() {
expect 112 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(112);
expect r0 <==> exists k :: 2 <= k < 112 && 112 % k == 0;
}
method {:test} Test24() {
expect 111 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(111);
expect r0 <==> exists k :: 2 <= k < 111 && 111 % k == 0;
}

// REPEAT 7 - TIME: 19.7903335 s

method {:test} Test25() {
expect 114 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(114);
expect r0 <==> exists k :: 2 <= k < 114 && 114 % k == 0;
}
method {:test} Test26() {
expect 113 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(113);
expect r0 <==> exists k :: 2 <= k < 113 && 113 % k == 0;
}

// REPEAT 8 - TIME: 21.0986963 s

method {:test} Test27() {
expect 116 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(116);
expect r0 <==> exists k :: 2 <= k < 116 && 116 % k == 0;
}
method {:test} Test28() {
expect 115 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(115);
expect r0 <==> exists k :: 2 <= k < 115 && 115 % k == 0;
}

// REPEAT 9 - TIME: 22.4262359 s

method {:test} Test29() {
expect 118 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(118);
expect r0 <==> exists k :: 2 <= k < 118 && 118 % k == 0;
}
method {:test} Test30() {
expect 117 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(117);
expect r0 <==> exists k :: 2 <= k < 117 && 117 % k == 0;
}

// REPEAT 10 - TIME: 23.5796282 s
