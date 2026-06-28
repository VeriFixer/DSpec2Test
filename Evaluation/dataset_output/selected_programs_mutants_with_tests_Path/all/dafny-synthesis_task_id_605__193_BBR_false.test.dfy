// dafny-synthesis_task_id_605.dfy

method {:testEntry} IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall k :: 2 <= k < n ==> n % k != 0
{
  result := true;
  var i := 2;
  while false
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
expect 2 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(2);
expect r0 <==> forall k :: 2 <= k < 2 ==> 2 % k != 0;
}
method {:test} Test1() {
expect 4 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(4);
expect r0 <==> forall k :: 2 <= k < 4 ==> 4 % k != 0;
}

// REPEAT 1 - TIME: 13.4070857 s

method {:test} Test2() {
expect 15444 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15444);
expect r0 <==> forall k :: 2 <= k < 15444 ==> 15444 % k != 0;
}
method {:test} Test3() {
expect 6 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(6);
expect r0 <==> forall k :: 2 <= k < 6 ==> 6 % k != 0;
}

// REPEAT 2 - TIME: 21.7398907 s

method {:test} Test4() {
expect 15446 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15446);
expect r0 <==> forall k :: 2 <= k < 15446 ==> 15446 % k != 0;
}

// REPEAT 3 - TIME: 29.623189 s

method {:test} Test6() {
expect 15448 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15448);
expect r0 <==> forall k :: 2 <= k < 15448 ==> 15448 % k != 0;
}

// REPEAT 4 - TIME: 37.8829849 s

method {:test} Test8() {
expect 15449 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15449);
expect r0 <==> forall k :: 2 <= k < 15449 ==> 15449 % k != 0;
}
method {:test} Test9() {
expect 15450 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15450);
expect r0 <==> forall k :: 2 <= k < 15450 ==> 15450 % k != 0;
}

// REPEAT 5 - TIME: 46.0636302 s

method {:test} Test10() {
expect 15451 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15451);
expect r0 <==> forall k :: 2 <= k < 15451 ==> 15451 % k != 0;
}
method {:test} Test11() {
expect 15452 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15452);
expect r0 <==> forall k :: 2 <= k < 15452 ==> 15452 % k != 0;
}

// REPEAT 6 - TIME: 54.4388677 s

method {:test} Test12() {
expect 15454 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15454);
expect r0 <==> forall k :: 2 <= k < 15454 ==> 15454 % k != 0;
}

// REPEAT 7 - TIME: 63.6591301 s

method {:test} Test14() {
expect 15456 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15456);
expect r0 <==> forall k :: 2 <= k < 15456 ==> 15456 % k != 0;
}

// REPEAT 8 - TIME: 71.0400213 s

method {:test} Test16() {
expect 15457 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15457);
expect r0 <==> forall k :: 2 <= k < 15457 ==> 15457 % k != 0;
}
method {:test} Test17() {
expect 15458 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15458);
expect r0 <==> forall k :: 2 <= k < 15458 ==> 15458 % k != 0;
}

// REPEAT 9 - TIME: 79.8431502 s

method {:test} Test18() {
expect 15459 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15459);
expect r0 <==> forall k :: 2 <= k < 15459 ==> 15459 % k != 0;
}
method {:test} Test19() {
expect 15460 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsPrime(15460);
expect r0 <==> forall k :: 2 <= k < 15460 ==> 15460 % k != 0;
}

// REPEAT 10 - TIME: 89.3173987 s
