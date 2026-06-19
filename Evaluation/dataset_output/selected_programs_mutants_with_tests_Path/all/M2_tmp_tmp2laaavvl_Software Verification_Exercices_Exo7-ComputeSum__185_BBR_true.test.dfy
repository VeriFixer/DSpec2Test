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
var r0 := ComputeSum(40);
expect r0 == Sum(40);
}

// REPEAT 1 - TIME: 7.1683786 s

method {:test} Test1() {
var r0 := ComputeSum(41);
expect r0 == Sum(41);
}

// REPEAT 2 - TIME: 12.6673047 s

method {:test} Test2() {
var r0 := ComputeSum(42);
expect r0 == Sum(42);
}

// REPEAT 3 - TIME: 16.594514 s

method {:test} Test3() {
var r0 := ComputeSum(43);
expect r0 == Sum(43);
}

// REPEAT 4 - TIME: 20.4578465 s

method {:test} Test4() {
var r0 := ComputeSum(44);
expect r0 == Sum(44);
}

// REPEAT 5 - TIME: 24.4255973 s

method {:test} Test5() {
var r0 := ComputeSum(45);
expect r0 == Sum(45);
}

// REPEAT 6 - TIME: 28.414434 s

method {:test} Test6() {
var r0 := ComputeSum(46);
expect r0 == Sum(46);
}

// REPEAT 7 - TIME: 32.8647666 s

method {:test} Test7() {
var r0 := ComputeSum(47);
expect r0 == Sum(47);
}

// REPEAT 8 - TIME: 36.8570513 s

method {:test} Test8() {
var r0 := ComputeSum(48);
expect r0 == Sum(48);
}

// REPEAT 9 - TIME: 40.7350474 s

method {:test} Test9() {
var r0 := ComputeSum(49);
expect r0 == Sum(49);
}

// REPEAT 10 - TIME: 44.9487831 s
