// dafny-synthesis_task_id_605.dfy

method {:testEntry} IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall k :: 2 <= k < n ==> n % k != 0
{
  result := true;
  var i := 2;
  while i < n / 2
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
