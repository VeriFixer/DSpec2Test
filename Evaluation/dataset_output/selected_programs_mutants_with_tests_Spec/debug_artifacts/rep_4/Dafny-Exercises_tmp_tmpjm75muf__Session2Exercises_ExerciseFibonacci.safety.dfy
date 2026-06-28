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

method {:test} Test9() {
var r0 := fibonacci1(2441);
expect r0 == fib(2441);
}
method {:test} Test10() {
var r0 := fibonacci2(2441);
expect r0 == fib(2441);
}
method {:test} Test11() {
var r0 := fibonacci3(2441);
expect r0 == fib(2441);
}

// REPEAT 4 - TIME: 10.2384809 s
