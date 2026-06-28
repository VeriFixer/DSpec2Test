// dafny-synthesis_task_id_605.dfy

method {:testEntry} IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall k :: 2 <= k < n ==> n % k != 0
{
  result := true;
  var i := 2;
  while i <= n / 2
    invariant 2 <= i
    invariant result <==> forall k :: 2 <= k < i ==> n % k != 0
  {
    break;
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
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(4);
expect r0 <==> forall k :: 2 <= k < 4 ==> 4 % k != 0;
}

// REPEAT 1 - TIME: 3.5013023 s

method {:test} Test2() {
expect 41 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(41);
expect r0 <==> forall k :: 2 <= k < 41 ==> 41 % k != 0;
}
method {:test} Test3() {
expect 42 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(42);
expect r0 <==> forall k :: 2 <= k < 42 ==> 42 % k != 0;
}

// REPEAT 2 - TIME: 4.8473933 s

method {:test} Test4() {
expect 43 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(43);
expect r0 <==> forall k :: 2 <= k < 43 ==> 43 % k != 0;
}
method {:test} Test5() {
expect 44 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(44);
expect r0 <==> forall k :: 2 <= k < 44 ==> 44 % k != 0;
}

// REPEAT 3 - TIME: 6.3536913 s

method {:test} Test6() {
expect 45 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(45);
expect r0 <==> forall k :: 2 <= k < 45 ==> 45 % k != 0;
}
method {:test} Test7() {
expect 46 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(46);
expect r0 <==> forall k :: 2 <= k < 46 ==> 46 % k != 0;
}

// REPEAT 4 - TIME: 7.7029229 s

method {:test} Test8() {
expect 47 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(47);
expect r0 <==> forall k :: 2 <= k < 47 ==> 47 % k != 0;
}
method {:test} Test9() {
expect 48 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(48);
expect r0 <==> forall k :: 2 <= k < 48 ==> 48 % k != 0;
}

// REPEAT 5 - TIME: 9.0319382 s

method {:test} Test10() {
expect 49 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(49);
expect r0 <==> forall k :: 2 <= k < 49 ==> 49 % k != 0;
}
method {:test} Test11() {
expect 50 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(50);
expect r0 <==> forall k :: 2 <= k < 50 ==> 50 % k != 0;
}

// REPEAT 6 - TIME: 10.0400912 s

method {:test} Test12() {
expect 51 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(51);
expect r0 <==> forall k :: 2 <= k < 51 ==> 51 % k != 0;
}
method {:test} Test13() {
expect 52 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(52);
expect r0 <==> forall k :: 2 <= k < 52 ==> 52 % k != 0;
}

// REPEAT 7 - TIME: 11.0659233 s

method {:test} Test14() {
expect 53 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(53);
expect r0 <==> forall k :: 2 <= k < 53 ==> 53 % k != 0;
}
method {:test} Test15() {
expect 54 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(54);
expect r0 <==> forall k :: 2 <= k < 54 ==> 54 % k != 0;
}

// REPEAT 8 - TIME: 11.8979469 s

method {:test} Test16() {
expect 55 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(55);
expect r0 <==> forall k :: 2 <= k < 55 ==> 55 % k != 0;
}
method {:test} Test17() {
expect 56 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(56);
expect r0 <==> forall k :: 2 <= k < 56 ==> 56 % k != 0;
}

// REPEAT 9 - TIME: 12.8643828 s

method {:test} Test18() {
expect 57 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(57);
expect r0 <==> forall k :: 2 <= k < 57 ==> 57 % k != 0;
}
method {:test} Test19() {
expect 58 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(58);
expect r0 <==> forall k :: 2 <= k < 58 ==> 58 % k != 0;
}

// REPEAT 10 - TIME: 13.6387945 s
