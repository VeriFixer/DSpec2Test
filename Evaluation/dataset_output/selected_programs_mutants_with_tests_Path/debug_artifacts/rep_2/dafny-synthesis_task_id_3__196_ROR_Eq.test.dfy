// dafny-synthesis_task_id_3.dfy

method {:testEntry} IsNonPrime(n: int) returns (result: bool)
  requires n >= 2
  ensures result <==> exists k :: 2 <= k < n && n % k == 0
{
  result := false;
  var i := 2;
  while i == n / 2
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

method {:test} Test2() {
expect 15444 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(15444);
expect r0 <==> exists k :: 2 <= k < 15444 && 15444 % k == 0;
}
method {:test} Test3() {
expect 6 >= 2, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsNonPrime(6);
expect r0 <==> exists k :: 2 <= k < 6 && 6 % k == 0;
}

// REPEAT 2 - TIME: 17.8168185 s
