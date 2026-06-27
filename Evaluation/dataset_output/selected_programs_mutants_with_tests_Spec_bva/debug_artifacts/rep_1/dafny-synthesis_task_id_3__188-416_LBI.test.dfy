// dafny-synthesis_task_id_3.dfy

method {:testEntry} IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k :: 2 <= k < n && n % k == 0
{
  result := false;
  var i := 2;
  while i <= n / 2
    invariant 2 <= i
    invariant result <==> exists k :: 2 <= k < i && n % k == 0
  {
    break;
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

// REPEAT 1 - TIME: 9.521649 s
