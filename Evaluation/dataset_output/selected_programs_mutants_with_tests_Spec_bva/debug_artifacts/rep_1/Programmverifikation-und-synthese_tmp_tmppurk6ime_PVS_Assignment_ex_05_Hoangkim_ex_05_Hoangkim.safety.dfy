
//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

method {:testEntry} fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
    a := 0;
    var b,x := 1,0;
    while x < n 
        invariant 0 <= x <= n
        invariant a == fib(x)
        invariant b == fib(x+1)
        {
            a,b := b,a+b;
            //why a,b := b,a+b is okay
            //but when I write  a := b;      //# Because this  
            //                  b := a+b;    //# is not the same  !! 
            //is error?                      //# {a = 1 , b = 2 } a := b ; b := a+b { b = 4 }, but 
            x := x+1;                        //# {a = 1 , b = 2 }   a, b := b,a+b  { b = 3 }
        }
    assert a == fib(n);     
}
//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

method {:testEntry} factIter(n:nat) returns (a:nat)
requires n >= 0;
ensures a == fact(n)
{
    a := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant a == fact(i-1)
    {
        a := a * i;
        i := i + 1;
    }
    assert a == fact(n);
} 
//# 3 pts
//Problem03
function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{
    if m == n then m
    else if m > n then gcd(m - n, n)
    else gcd(m, n - m)
}

method {:testEntry} gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
    {
        var x: int;
        g := m;
        x := n;
        while (g != x)
        invariant x > 0;
        invariant g > 0;
        invariant gcd(g, x) == gcd(m, n);
        decreases x+g;
        {
          if (g > x)
          {
             g := g - x;
          }
          else
          {
             x := x - g;
          }
        }
    }
//# 3 pts


// # sum: 9 pts

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1);
expect r0 == fib(1);
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(100);
expect r0 == fib(100);
}
method {:test} Test4() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(3);
expect r0 == fib(3);
}
method {:test} Test7() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(2);
expect r0 == fact(2);
}
method {:test} Test8() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(0);
expect r0 == fact(0);
}
method {:test} Test9() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(100);
expect r0 == fact(100);
}
method {:test} Test14() {
expect 16677 > 0 && 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16677, 7720);
expect r0 == gcd(16677, 7720);
}
method {:test} Test15() {
expect 1 > 0 && 1239 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(1, 1239);
expect r0 == gcd(1, 1239);
}
method {:test} Test16() {
expect 100 > 0 && 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(100, 201);
expect r0 == gcd(100, 201);
}
method {:test} Test17() {
expect 1239 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(1239, 1);
expect r0 == gcd(1239, 1);
}
method {:test} Test18() {
expect 201 > 0 && 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(201, 100);
expect r0 == gcd(201, 100);
}

// REPEAT 1 - TIME: 14.1370022 s
