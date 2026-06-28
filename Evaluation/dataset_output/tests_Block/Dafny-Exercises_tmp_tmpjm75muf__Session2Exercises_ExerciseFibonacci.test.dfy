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
var r0 := fibonacci2(8861);
expect r0 == fib(8861);
}
method {:test} Test2() {
var r0 := fibonacci2(0);
expect r0 == fib(0);
}
method {:test} Test3() {
var r0 := fibonacci3(8861);
expect r0 == fib(8861);
}

// REPEAT 1 - TIME: 3.2286751 s

method {:test} Test4() {
var r0 := fibonacci1(2);
expect r0 == fib(2);
}
method {:test} Test5() {
var r0 := fibonacci2(8862);
expect r0 == fib(8862);
}
method {:test} Test7() {
var r0 := fibonacci3(8862);
expect r0 == fib(8862);
}

// REPEAT 2 - TIME: 4.9677582 s

method {:test} Test8() {
var r0 := fibonacci1(3);
expect r0 == fib(3);
}
method {:test} Test9() {
var r0 := fibonacci2(8863);
expect r0 == fib(8863);
}
method {:test} Test11() {
var r0 := fibonacci3(8863);
expect r0 == fib(8863);
}

// REPEAT 3 - TIME: 6.8199431 s

method {:test} Test12() {
var r0 := fibonacci1(4);
expect r0 == fib(4);
}
method {:test} Test13() {
var r0 := fibonacci2(8864);
expect r0 == fib(8864);
}
method {:test} Test15() {
var r0 := fibonacci3(8864);
expect r0 == fib(8864);
}

// REPEAT 4 - TIME: 8.5387371 s

method {:test} Test16() {
var r0 := fibonacci1(5);
expect r0 == fib(5);
}
method {:test} Test17() {
var r0 := fibonacci2(8865);
expect r0 == fib(8865);
}
method {:test} Test19() {
var r0 := fibonacci3(8865);
expect r0 == fib(8865);
}

// REPEAT 5 - TIME: 9.8843785 s

method {:test} Test20() {
var r0 := fibonacci1(6);
expect r0 == fib(6);
}
method {:test} Test21() {
var r0 := fibonacci2(8866);
expect r0 == fib(8866);
}
method {:test} Test23() {
var r0 := fibonacci3(8866);
expect r0 == fib(8866);
}

// REPEAT 6 - TIME: 11.3938025 s

method {:test} Test24() {
var r0 := fibonacci1(7);
expect r0 == fib(7);
}
method {:test} Test25() {
var r0 := fibonacci2(8867);
expect r0 == fib(8867);
}
method {:test} Test27() {
var r0 := fibonacci3(8867);
expect r0 == fib(8867);
}

// REPEAT 7 - TIME: 12.5508528 s

method {:test} Test28() {
var r0 := fibonacci1(8);
expect r0 == fib(8);
}
method {:test} Test29() {
var r0 := fibonacci2(8868);
expect r0 == fib(8868);
}
method {:test} Test31() {
var r0 := fibonacci3(8868);
expect r0 == fib(8868);
}

// REPEAT 8 - TIME: 13.736176 s

method {:test} Test32() {
var r0 := fibonacci1(9);
expect r0 == fib(9);
}
method {:test} Test33() {
var r0 := fibonacci2(8869);
expect r0 == fib(8869);
}
method {:test} Test35() {
var r0 := fibonacci3(8869);
expect r0 == fib(8869);
}

// REPEAT 9 - TIME: 14.8445083 s

method {:test} Test36() {
var r0 := fibonacci1(10);
expect r0 == fib(10);
}
method {:test} Test37() {
var r0 := fibonacci2(8870);
expect r0 == fib(8870);
}
method {:test} Test39() {
var r0 := fibonacci3(8870);
expect r0 == fib(8870);
}

// REPEAT 10 - TIME: 16.235198 s
