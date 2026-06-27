// dafny-synthesis_task_id_605.dfy

method {:testEntry} IsPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> forall k :: 2 <= k < n ==> n % k != 0
{
  result := true;
  var i := 2;
  while i <= n * 2
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

// REPEAT 2 - TIME: 5.1301222 s
