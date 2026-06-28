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
expect 40 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(40);
expect r0 <==> forall k :: 2 <= k < 40 ==> 40 % k != 0;
}
method {:test} Test1() {
expect 2 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2);
expect r0 <==> forall k :: 2 <= k < 2 ==> 2 % k != 0;
}
method {:test} Test2() {
expect 100 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(100);
expect r0 <==> forall k :: 2 <= k < 100 ==> 100 % k != 0;
}
method {:test} Test7() {
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(4);
expect r0 <==> forall k :: 2 <= k < 4 ==> 4 % k != 0;
}
method {:test} Test12() {
expect 6 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(6);
expect r0 <==> forall k :: 2 <= k < 6 ==> 6 % k != 0;
}

// REPEAT 1 - TIME: 12.6577253 s

method {:test} Test13() {
expect 101 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(101);
expect r0 <==> forall k :: 2 <= k < 101 ==> 101 % k != 0;
}
method {:test} Test14() {
expect 102 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(102);
expect r0 <==> forall k :: 2 <= k < 102 ==> 102 % k != 0;
}

// REPEAT 2 - TIME: 14.2414081 s

method {:test} Test15() {
expect 103 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(103);
expect r0 <==> forall k :: 2 <= k < 103 ==> 103 % k != 0;
}
method {:test} Test16() {
expect 104 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(104);
expect r0 <==> forall k :: 2 <= k < 104 ==> 104 % k != 0;
}

// REPEAT 3 - TIME: 15.5848768 s

method {:test} Test17() {
expect 105 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(105);
expect r0 <==> forall k :: 2 <= k < 105 ==> 105 % k != 0;
}
method {:test} Test18() {
expect 106 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(106);
expect r0 <==> forall k :: 2 <= k < 106 ==> 106 % k != 0;
}

// REPEAT 4 - TIME: 17.0958011 s

method {:test} Test19() {
expect 107 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(107);
expect r0 <==> forall k :: 2 <= k < 107 ==> 107 % k != 0;
}
method {:test} Test20() {
expect 108 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(108);
expect r0 <==> forall k :: 2 <= k < 108 ==> 108 % k != 0;
}

// REPEAT 5 - TIME: 18.4336187 s

method {:test} Test21() {
expect 109 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(109);
expect r0 <==> forall k :: 2 <= k < 109 ==> 109 % k != 0;
}
method {:test} Test22() {
expect 110 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(110);
expect r0 <==> forall k :: 2 <= k < 110 ==> 110 % k != 0;
}

// REPEAT 6 - TIME: 19.7609115 s

method {:test} Test23() {
expect 111 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(111);
expect r0 <==> forall k :: 2 <= k < 111 ==> 111 % k != 0;
}
method {:test} Test24() {
expect 112 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(112);
expect r0 <==> forall k :: 2 <= k < 112 ==> 112 % k != 0;
}

// REPEAT 7 - TIME: 21.1115782 s

method {:test} Test25() {
expect 113 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(113);
expect r0 <==> forall k :: 2 <= k < 113 ==> 113 % k != 0;
}
method {:test} Test26() {
expect 114 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(114);
expect r0 <==> forall k :: 2 <= k < 114 ==> 114 % k != 0;
}

// REPEAT 8 - TIME: 22.271289 s

method {:test} Test27() {
expect 115 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(115);
expect r0 <==> forall k :: 2 <= k < 115 ==> 115 % k != 0;
}
method {:test} Test28() {
expect 116 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(116);
expect r0 <==> forall k :: 2 <= k < 116 ==> 116 % k != 0;
}

// REPEAT 9 - TIME: 23.4920856 s

method {:test} Test29() {
expect 117 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(117);
expect r0 <==> forall k :: 2 <= k < 117 ==> 117 % k != 0;
}
method {:test} Test30() {
expect 118 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(118);
expect r0 <==> forall k :: 2 <= k < 118 ==> 118 % k != 0;
}

// REPEAT 10 - TIME: 24.6618161 s
