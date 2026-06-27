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
var r0 := fibonacci1(1800);
expect r0 == fib(1800);
}
method {:test} Test1() {
var r0 := fibonacci2(0);
expect r0 == fib(0);
}
method {:test} Test2() {
var r0 := fibonacci2(1241);
expect r0 == fib(1241);
}
method {:test} Test3() {
var r0 := fibonacci3(1241);
expect r0 == fib(1241);
}

// REPEAT 1 - TIME: 18.9574933 s

method {:test} Test4() {
var r0 := fibonacci1(1801);
expect r0 == fib(1801);
}
method {:test} Test5() {
var r0 := fibonacci2(1242);
expect r0 == fib(1242);
}
method {:test} Test6() {
var r0 := fibonacci3(1242);
expect r0 == fib(1242);
}

// REPEAT 2 - TIME: 34.163424 s

method {:test} Test7() {
var r0 := fibonacci1(1802);
expect r0 == fib(1802);
}
method {:test} Test8() {
var r0 := fibonacci2(1243);
expect r0 == fib(1243);
}
method {:test} Test9() {
var r0 := fibonacci3(1243);
expect r0 == fib(1243);
}

// REPEAT 3 - TIME: 48.5037524 s

method {:test} Test10() {
var r0 := fibonacci1(1803);
expect r0 == fib(1803);
}
method {:test} Test11() {
var r0 := fibonacci2(1244);
expect r0 == fib(1244);
}
method {:test} Test12() {
var r0 := fibonacci3(1244);
expect r0 == fib(1244);
}

// REPEAT 4 - TIME: 63.2626858 s

method {:test} Test13() {
var r0 := fibonacci1(1804);
expect r0 == fib(1804);
}
method {:test} Test14() {
var r0 := fibonacci2(1245);
expect r0 == fib(1245);
}
method {:test} Test15() {
var r0 := fibonacci3(1245);
expect r0 == fib(1245);
}

// REPEAT 5 - TIME: 78.1524018 s

method {:test} Test16() {
var r0 := fibonacci1(1805);
expect r0 == fib(1805);
}
method {:test} Test17() {
var r0 := fibonacci2(1246);
expect r0 == fib(1246);
}
method {:test} Test18() {
var r0 := fibonacci3(1246);
expect r0 == fib(1246);
}

// REPEAT 6 - TIME: 94.6065133 s

method {:test} Test19() {
var r0 := fibonacci1(1806);
expect r0 == fib(1806);
}
method {:test} Test20() {
var r0 := fibonacci2(1247);
expect r0 == fib(1247);
}
method {:test} Test21() {
var r0 := fibonacci3(1247);
expect r0 == fib(1247);
}

// REPEAT 7 - TIME: 114.6614536 s

method {:test} Test22() {
var r0 := fibonacci1(1807);
expect r0 == fib(1807);
}
method {:test} Test23() {
var r0 := fibonacci2(1248);
expect r0 == fib(1248);
}
method {:test} Test24() {
var r0 := fibonacci3(1248);
expect r0 == fib(1248);
}

// REPEAT 8 - TIME: 141.7026785 s

method {:test} Test25() {
var r0 := fibonacci1(1808);
expect r0 == fib(1808);
}
method {:test} Test26() {
var r0 := fibonacci2(1249);
expect r0 == fib(1249);
}
method {:test} Test27() {
var r0 := fibonacci3(1249);
expect r0 == fib(1249);
}

// REPEAT 9 - TIME: 173.3303543 s

method {:test} Test28() {
var r0 := fibonacci1(1809);
expect r0 == fib(1809);
}
method {:test} Test29() {
var r0 := fibonacci2(1250);
expect r0 == fib(1250);
}
method {:test} Test30() {
var r0 := fibonacci3(1250);
expect r0 == fib(1250);
}

// REPEAT 10 - TIME: 216.0928504 s
