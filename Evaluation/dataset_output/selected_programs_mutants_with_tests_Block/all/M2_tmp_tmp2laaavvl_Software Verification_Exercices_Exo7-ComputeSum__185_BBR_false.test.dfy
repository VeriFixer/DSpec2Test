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
  while false
    invariant 0 <= i <= n
    invariant s == Sum(i)
  {
    s := s + i + 1;
    i := i + 1;
  }
}


method {:test} Test0() {
var r0 := ComputeSum(1);
expect r0 == Sum(1);
}

// REPEAT 1 - TIME: 1.9563749 s

method {:test} Test1() {
var r0 := ComputeSum(2);
expect r0 == Sum(2);
}

// REPEAT 2 - TIME: 2.624389 s

method {:test} Test2() {
var r0 := ComputeSum(3);
expect r0 == Sum(3);
}

// REPEAT 3 - TIME: 3.5125798 s

method {:test} Test3() {
var r0 := ComputeSum(4);
expect r0 == Sum(4);
}

// REPEAT 4 - TIME: 4.1569599 s

method {:test} Test4() {
var r0 := ComputeSum(5);
expect r0 == Sum(5);
}

// REPEAT 5 - TIME: 4.7587487 s

method {:test} Test5() {
var r0 := ComputeSum(6);
expect r0 == Sum(6);
}

// REPEAT 6 - TIME: 5.3609902 s

method {:test} Test6() {
var r0 := ComputeSum(7);
expect r0 == Sum(7);
}

// REPEAT 7 - TIME: 5.9608733 s

method {:test} Test7() {
var r0 := ComputeSum(8);
expect r0 == Sum(8);
}

// REPEAT 8 - TIME: 6.7244144 s

method {:test} Test8() {
var r0 := ComputeSum(9);
expect r0 == Sum(9);
}

// REPEAT 9 - TIME: 7.4865664 s

method {:test} Test9() {
var r0 := ComputeSum(10);
expect r0 == Sum(10);
}

// REPEAT 10 - TIME: 7.9485674 s
