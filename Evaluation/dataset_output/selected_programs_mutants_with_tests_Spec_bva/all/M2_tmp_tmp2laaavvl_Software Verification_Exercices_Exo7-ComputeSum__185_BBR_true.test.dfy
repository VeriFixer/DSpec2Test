// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo7-ComputeSum.dfy

function Sum(n: nat): nat
{
  if n == 0 then
    0
  else
    n + Sum(n - 1)
}

method {:testEntry} ComputeSum(n: nat) returns (s: nat)
  ensures s == Sum(n)
{
  s := 0;
  var i := 0;
  while true
    invariant 0 <= i <= n
    invariant s == Sum(i)
  {
    s := s + i + 1;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := ComputeSum(7721);
expect r0 == Sum(7721);
}
method {:test} Test1() {
var r0 := ComputeSum(100);
expect r0 == Sum(100);
}
method {:test} Test3() {
var r0 := ComputeSum(24);
expect r0 == Sum(24);
}

// REPEAT 1 - TIME: 8.6277161 s

method {:test} Test6() {
var r0 := ComputeSum(7722);
expect r0 == Sum(7722);
}

// REPEAT 2 - TIME: 9.9336909 s

method {:test} Test7() {
var r0 := ComputeSum(7723);
expect r0 == Sum(7723);
}

// REPEAT 3 - TIME: 11.0749618 s

method {:test} Test8() {
var r0 := ComputeSum(7724);
expect r0 == Sum(7724);
}

// REPEAT 4 - TIME: 12.2459059 s

method {:test} Test9() {
var r0 := ComputeSum(7725);
expect r0 == Sum(7725);
}

// REPEAT 5 - TIME: 13.1844907 s

method {:test} Test10() {
var r0 := ComputeSum(7726);
expect r0 == Sum(7726);
}

// REPEAT 6 - TIME: 14.1720515 s

method {:test} Test11() {
var r0 := ComputeSum(7727);
expect r0 == Sum(7727);
}

// REPEAT 7 - TIME: 15.2442835 s

method {:test} Test12() {
var r0 := ComputeSum(7728);
expect r0 == Sum(7728);
}

// REPEAT 8 - TIME: 16.1885341 s

method {:test} Test13() {
var r0 := ComputeSum(7729);
expect r0 == Sum(7729);
}

// REPEAT 9 - TIME: 16.9839553 s

method {:test} Test14() {
var r0 := ComputeSum(7730);
expect r0 == Sum(7730);
}

// REPEAT 10 - TIME: 17.8841225 s
