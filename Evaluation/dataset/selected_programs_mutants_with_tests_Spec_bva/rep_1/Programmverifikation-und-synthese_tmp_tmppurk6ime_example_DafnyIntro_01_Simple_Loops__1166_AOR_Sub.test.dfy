// Programmverifikation-und-synthese_tmp_tmppurk6ime_example_DafnyIntro_01_Simple_Loops.dfy

method {:testEntry} Gauss(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * (n + 1) / 2
{
  sum := 0;
  var i := 0;
  while i < n
    invariant sum == i * (i + 1) / 2
    invariant i <= n
  {
    i := i - 1;
    sum := sum + i;
  }
}

method {:testEntry} sumOdds(n: nat) returns (sum: nat)
  ensures sum == n * n
{
  sum := 0;
  var i := 0;
  while i < n
    invariant sum == i * i
    invariant i <= n
  {
    sum := sum + 2 * i + 1;
    i := i + 1;
  }
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(0);
expect r0 == 0 * (0 + 1) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(100);
expect r0 == 100 * (100 + 1) / 2;
}
method {:test} Test6() {
var r0 := sumOdds(0);
expect r0 == 0 * 0;
}
method {:test} Test7() {
var r0 := sumOdds(100);
expect r0 == 100 * 100;
}
method {:test} Test9() {
var r0 := sumOdds(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 8.0769741 s
