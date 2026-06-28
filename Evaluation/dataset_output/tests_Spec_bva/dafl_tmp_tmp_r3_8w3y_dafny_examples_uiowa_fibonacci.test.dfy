/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
function fib(n: nat): nat
  decreases n;
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}

method {:testEntry} ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{
  if (n == 0) 
    { f := 0; }
  else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
        f   := 1;    
    while (i < n) 
      decreases n - i;
      invariant i <= n;
      invariant f_1 == fib(i - 1);
      invariant f   == fib(i);
    {
      f_2 := f_1;
      f_1 := f; 
      f   := f_1 + f_2;

      i := i + 1;
    }
  }
}

method {:test} Test0() {
var r0 := ComputeFib(1);
expect r0 == fib(1);
}
method {:test} Test1() {
var r0 := ComputeFib(100);
expect r0 == fib(100);
}
method {:test} Test3() {
var r0 := ComputeFib(3);
expect r0 == fib(3);
}
method {:test} Test4() {
var r0 := ComputeFib(2441);
expect r0 == fib(2441);
}

// REPEAT 1 - TIME: 7.9065837 s

method {:test} Test6() {
var r0 := ComputeFib(2442);
expect r0 == fib(2442);
}

// REPEAT 2 - TIME: 9.212183 s

method {:test} Test7() {
var r0 := ComputeFib(2443);
expect r0 == fib(2443);
}

// REPEAT 3 - TIME: 10.4870235 s

method {:test} Test8() {
var r0 := ComputeFib(2444);
expect r0 == fib(2444);
}

// REPEAT 4 - TIME: 11.5553459 s

method {:test} Test9() {
var r0 := ComputeFib(2445);
expect r0 == fib(2445);
}

// REPEAT 5 - TIME: 12.4686033 s

method {:test} Test10() {
var r0 := ComputeFib(2446);
expect r0 == fib(2446);
}

// REPEAT 6 - TIME: 13.748958 s

method {:test} Test11() {
var r0 := ComputeFib(2447);
expect r0 == fib(2447);
}

// REPEAT 7 - TIME: 14.709951 s

method {:test} Test12() {
var r0 := ComputeFib(2448);
expect r0 == fib(2448);
}

// REPEAT 8 - TIME: 15.710555 s

method {:test} Test13() {
var r0 := ComputeFib(2449);
expect r0 == fib(2449);
}

// REPEAT 9 - TIME: 16.5458368 s

method {:test} Test14() {
var r0 := ComputeFib(2450);
expect r0 == fib(2450);
}

// REPEAT 10 - TIME: 17.4216759 s
