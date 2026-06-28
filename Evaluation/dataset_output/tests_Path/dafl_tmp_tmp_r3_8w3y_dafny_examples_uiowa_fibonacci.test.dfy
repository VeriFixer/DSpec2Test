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
var r0 := ComputeFib(0);
expect r0 == fib(0);
}
method {:test} Test1() {
var r0 := ComputeFib(1241);
expect r0 == fib(1241);
}

// REPEAT 1 - TIME: 4.5625425 s

method {:test} Test2() {
var r0 := ComputeFib(1242);
expect r0 == fib(1242);
}

// REPEAT 2 - TIME: 7.1805731 s

method {:test} Test3() {
var r0 := ComputeFib(1243);
expect r0 == fib(1243);
}

// REPEAT 3 - TIME: 9.0418382 s

method {:test} Test4() {
var r0 := ComputeFib(1244);
expect r0 == fib(1244);
}

// REPEAT 4 - TIME: 10.8282107 s

method {:test} Test5() {
var r0 := ComputeFib(1245);
expect r0 == fib(1245);
}

// REPEAT 5 - TIME: 12.6095527 s

method {:test} Test6() {
var r0 := ComputeFib(1246);
expect r0 == fib(1246);
}

// REPEAT 6 - TIME: 14.8673967 s

method {:test} Test7() {
var r0 := ComputeFib(1247);
expect r0 == fib(1247);
}

// REPEAT 7 - TIME: 16.7878594 s

method {:test} Test8() {
var r0 := ComputeFib(1248);
expect r0 == fib(1248);
}

// REPEAT 8 - TIME: 18.8242535 s

method {:test} Test9() {
var r0 := ComputeFib(1249);
expect r0 == fib(1249);
}

// REPEAT 9 - TIME: 20.61572 s

method {:test} Test10() {
var r0 := ComputeFib(1250);
expect r0 == fib(1250);
}

// REPEAT 10 - TIME: 23.0719159 s
