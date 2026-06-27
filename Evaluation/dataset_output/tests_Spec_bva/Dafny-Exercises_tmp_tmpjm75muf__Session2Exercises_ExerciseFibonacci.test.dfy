function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method {:testEntry} fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
{
   var i := 0;
   f := 0;
   var fsig := 1;
   while i < n
      decreases n - i//write the bound
      invariant f==fib(i) && fsig==fib(i+1)//write the invariant
      invariant i<=n
   {
      f, fsig := fsig, f + fsig;
      i := i + 1;
   }
}

method {:testEntry} fibonacci2(n:nat) returns (f:nat)
ensures f==fib(n)
{
if (n==0) {f:=0;}
else{
   var i := 1;
   var fant := 0;
   f := 1;
   while i < n
      decreases n-i//write the bound
      invariant fant==fib(i-1) && f==fib(i)//write the invariant
      invariant i<=n
   {
      fant, f := f, fant + f;
      i := i + 1;
   }
}

}

method {:testEntry} fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
{

{
   var i: int := 0;
   var a := 1;
       f := 0; 
   while i < n
    decreases n-i//write the bound
    invariant 0<=i<=n
    invariant if i ==0 then a==fib(i+1) && f==fib(i)//write the invariant 
               else a==fib(i-1) && f==fib(i)
   {
      a, f := f, a + f; 
      i := i + 1;
   }
}
}

method {:test} Test0() {
var r0 := fibonacci1(1);
expect r0 == fib(1);
}
method {:test} Test1() {
var r0 := fibonacci1(100);
expect r0 == fib(100);
}
method {:test} Test3() {
var r0 := fibonacci1(3);
expect r0 == fib(3);
}
method {:test} Test4() {
var r0 := fibonacci1(2441);
expect r0 == fib(2441);
}
method {:test} Test6() {
var r0 := fibonacci2(1);
expect r0 == fib(1);
}
method {:test} Test7() {
var r0 := fibonacci2(100);
expect r0 == fib(100);
}
method {:test} Test9() {
var r0 := fibonacci2(3);
expect r0 == fib(3);
}
method {:test} Test10() {
var r0 := fibonacci2(2441);
expect r0 == fib(2441);
}
method {:test} Test12() {
var r0 := fibonacci3(1);
expect r0 == fib(1);
}
method {:test} Test13() {
var r0 := fibonacci3(100);
expect r0 == fib(100);
}
method {:test} Test15() {
var r0 := fibonacci3(3);
expect r0 == fib(3);
}
method {:test} Test16() {
var r0 := fibonacci3(2441);
expect r0 == fib(2441);
}

// REPEAT 1 - TIME: 13.0027782 s

method {:test} Test18() {
var r0 := fibonacci1(2442);
expect r0 == fib(2442);
}
method {:test} Test19() {
var r0 := fibonacci2(2442);
expect r0 == fib(2442);
}
method {:test} Test20() {
var r0 := fibonacci3(2442);
expect r0 == fib(2442);
}

// REPEAT 2 - TIME: 14.6074345 s

method {:test} Test21() {
var r0 := fibonacci1(2443);
expect r0 == fib(2443);
}
method {:test} Test22() {
var r0 := fibonacci2(2443);
expect r0 == fib(2443);
}
method {:test} Test23() {
var r0 := fibonacci3(2443);
expect r0 == fib(2443);
}

// REPEAT 3 - TIME: 16.3001135 s

method {:test} Test24() {
var r0 := fibonacci1(2444);
expect r0 == fib(2444);
}
method {:test} Test25() {
var r0 := fibonacci2(2444);
expect r0 == fib(2444);
}
method {:test} Test26() {
var r0 := fibonacci3(2444);
expect r0 == fib(2444);
}

// REPEAT 4 - TIME: 17.7855597 s

method {:test} Test27() {
var r0 := fibonacci1(2445);
expect r0 == fib(2445);
}
method {:test} Test28() {
var r0 := fibonacci2(2445);
expect r0 == fib(2445);
}
method {:test} Test29() {
var r0 := fibonacci3(2445);
expect r0 == fib(2445);
}

// REPEAT 5 - TIME: 19.2092917 s

method {:test} Test30() {
var r0 := fibonacci1(2446);
expect r0 == fib(2446);
}
method {:test} Test31() {
var r0 := fibonacci2(2446);
expect r0 == fib(2446);
}
method {:test} Test32() {
var r0 := fibonacci3(2446);
expect r0 == fib(2446);
}

// REPEAT 6 - TIME: 20.5656605 s

method {:test} Test33() {
var r0 := fibonacci1(2447);
expect r0 == fib(2447);
}
method {:test} Test34() {
var r0 := fibonacci2(2447);
expect r0 == fib(2447);
}
method {:test} Test35() {
var r0 := fibonacci3(2447);
expect r0 == fib(2447);
}

// REPEAT 7 - TIME: 21.7824722 s

method {:test} Test36() {
var r0 := fibonacci1(2448);
expect r0 == fib(2448);
}
method {:test} Test37() {
var r0 := fibonacci2(2448);
expect r0 == fib(2448);
}
method {:test} Test38() {
var r0 := fibonacci3(2448);
expect r0 == fib(2448);
}

// REPEAT 8 - TIME: 22.9349888 s

method {:test} Test39() {
var r0 := fibonacci1(2449);
expect r0 == fib(2449);
}
method {:test} Test40() {
var r0 := fibonacci2(2449);
expect r0 == fib(2449);
}
method {:test} Test41() {
var r0 := fibonacci3(2449);
expect r0 == fib(2449);
}

// REPEAT 9 - TIME: 24.2008651 s

method {:test} Test42() {
var r0 := fibonacci1(2450);
expect r0 == fib(2450);
}
method {:test} Test43() {
var r0 := fibonacci2(2450);
expect r0 == fib(2450);
}
method {:test} Test44() {
var r0 := fibonacci3(2450);
expect r0 == fib(2450);
}

// REPEAT 10 - TIME: 25.3707413 s
