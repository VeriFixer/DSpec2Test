// ****************************************************************************************
//                              DafnyIntro.dfy
// ****************************************************************************************
// We write a program to sum all numbers from 1 to n
// 
//  Gauss' formula states that 1 + 2 + 3 + ... + (n-1) + n == n*(n+1)/2 
//
// We take this a specification, thus in effect we use Dafny to prove Gauss' formula: 

// In essence Dafny does an inductive proof. It needs help with a loop "invariant".
// This is a condition which is 

// - true at the beginning of the loop
// - maintained with each passage through the loop body.

// These requirements correspond to an inductive proof

// - the invariant is the inductive hypothesis H(i)
// - it must be true for i=0
// - it must remain true when stepping from i to i+1,    

// Here we use two invariants I1 and I2, which amounts to the same as using I1 && I2:   

method {:testEntry} Gauss(n:int) returns (sum:int)
requires n >= 0
ensures sum == n*(n+1)/2     // 
{
  sum := 0; 
  var i := 0;
  while i < n
    invariant sum == i*(i+1)/2  
    invariant i <= n
  {
      i := i+1;
    sum := sum + i;
  }
}

// As a second example, we add the first n odd numbers 
// This yields n*n, i.e.
//
//      1 + 3 + 5 + 7 + 9 + 11 + ... 2n+1 == n*n
//
// Here is the proof using Dafny:

method {:testEntry} sumOdds(n:nat) returns (sum:nat)
ensures sum == n*n;
{
     sum := 0; 
  var  i := 0;
  while i < n
    invariant sum == i*i   // the inductive hypothesis
    invariant i <= n
  {
    sum := sum + 2*i+1;
      i := i+1;            // the step from i to i+1
  }
}

// This verifies, so the proof is complete !!

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

// REPEAT 1 - TIME: 9.5654085 s

method {:test} Test12() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(101);
expect r0 == 101 * (101 + 1) / 2;
}
method {:test} Test13() {
var r0 := sumOdds(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 10.624834 s

method {:test} Test14() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(102);
expect r0 == 102 * (102 + 1) / 2;
}
method {:test} Test15() {
var r0 := sumOdds(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 11.566611 s

method {:test} Test16() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(103);
expect r0 == 103 * (103 + 1) / 2;
}
method {:test} Test17() {
var r0 := sumOdds(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 12.5893327 s

method {:test} Test18() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(104);
expect r0 == 104 * (104 + 1) / 2;
}
method {:test} Test19() {
var r0 := sumOdds(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 13.5595795 s

method {:test} Test20() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(105);
expect r0 == 105 * (105 + 1) / 2;
}
method {:test} Test21() {
var r0 := sumOdds(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 14.5876487 s

method {:test} Test22() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(106);
expect r0 == 106 * (106 + 1) / 2;
}
method {:test} Test23() {
var r0 := sumOdds(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 15.57207 s

method {:test} Test24() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(107);
expect r0 == 107 * (107 + 1) / 2;
}
method {:test} Test25() {
var r0 := sumOdds(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 16.7401876 s

method {:test} Test26() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(108);
expect r0 == 108 * (108 + 1) / 2;
}
method {:test} Test27() {
var r0 := sumOdds(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 17.6159837 s

method {:test} Test28() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Gauss(109);
expect r0 == 109 * (109 + 1) / 2;
}
method {:test} Test29() {
var r0 := sumOdds(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 18.5090732 s
