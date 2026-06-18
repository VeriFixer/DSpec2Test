// Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_05_Hoangkim_ex_05_Hoangkim.dfy

function fib(n: nat): nat
{
  if n < 2 then
    n
  else
    fib(n - 2) + fib(n - 1)
}

method {:testEntry} fibIter(n: nat) returns (a: nat)
  requires n > 0
  ensures a == fib(n)
{
  a := 0;
  var b, x := 1, 0;
  while x < n
    invariant 0 <= x <= n
    invariant a == fib(x)
    invariant b == fib(x + 1)
  {
    a, b := b, a * b;
    x := x + 1;
  }
  assert a == fib(n);
}

function fact(n: nat): nat
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}

method {:testEntry} factIter(n: nat) returns (a: nat)
  requires n >= 0
  ensures a == fact(n)
{
  a := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant a == fact(i - 1)
  {
    a := a * i;
    i := i + 1;
  }
  assert a == fact(n);
}

function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
{
  if m == n then
    m
  else if m > n then
    gcd(m - n, n)
  else
    gcd(m, n - m)
}

method {:testEntry} gcdI(m: int, n: int) returns (g: int)
  requires m > 0 && n > 0
  ensures g == gcd(m, n)
{
  var x: int;
  g := m;
  x := n;
  while g != x
    invariant x > 0
    invariant g > 0
    invariant gcd(g, x) == gcd(m, n)
    decreases x + g
  {
    if g > x {
      g := g - x;
    } else {
      x := x - g;
    }
  }
}



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
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(2);
expect r0 == fact(2);
}
method {:test} Test2() {
expect 16677 > 0 && 7720 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(16677, 7720);
expect r0 == gcd(16677, 7720);
}

// REPEAT 1 - TIME: 3.7477382 s

method {:test} Test3() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(2);
expect r0 == fib(2);
}
method {:test} Test4() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(3);
expect r0 == fact(3);
}
method {:test} Test5() {
expect 20270 > 0 && 10135 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20270, 10135);
expect r0 == gcd(20270, 10135);
}

// REPEAT 2 - TIME: 5.8057407 s

method {:test} Test6() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(3);
expect r0 == fib(3);
}
method {:test} Test7() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(4);
expect r0 == fact(4);
}
method {:test} Test8() {
expect 20273 > 0 && 10136 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20273, 10136);
expect r0 == gcd(20273, 10136);
}

// REPEAT 3 - TIME: 7.9994283 s

method {:test} Test9() {
expect 1240 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1240);
expect r0 == fib(1240);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test11() {
expect 20275 > 0 && 10137 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20275, 10137);
expect r0 == gcd(20275, 10137);
}

// REPEAT 4 - TIME: 9.6102939 s

method {:test} Test12() {
expect 1241 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1241);
expect r0 == fib(1241);
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test14() {
expect 23868 > 0 && 11934 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23868, 11934);
expect r0 == gcd(23868, 11934);
}

// REPEAT 5 - TIME: 11.0561461 s

method {:test} Test15() {
expect 1242 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1242);
expect r0 == fib(1242);
}
method {:test} Test16() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test17() {
expect 23870 > 0 && 11935 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23870, 11935);
expect r0 == gcd(23870, 11935);
}

// REPEAT 6 - TIME: 12.2023382 s

method {:test} Test18() {
expect 1243 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1243);
expect r0 == fib(1243);
}
method {:test} Test19() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test20() {
expect 23873 > 0 && 11936 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23873, 11936);
expect r0 == gcd(23873, 11936);
}

// REPEAT 7 - TIME: 13.6802661 s

method {:test} Test21() {
expect 1244 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1244);
expect r0 == fib(1244);
}
method {:test} Test22() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test23() {
expect 23875 > 0 && 11937 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23875, 11937);
expect r0 == gcd(23875, 11937);
}

// REPEAT 8 - TIME: 14.8996232 s

method {:test} Test24() {
expect 1245 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1245);
expect r0 == fib(1245);
}
method {:test} Test25() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test26() {
expect 23877 > 0 && 11938 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23877, 11938);
expect r0 == gcd(23877, 11938);
}

// REPEAT 9 - TIME: 16.3396842 s

method {:test} Test27() {
expect 1246 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(1246);
expect r0 == fib(1246);
}
method {:test} Test28() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test29() {
expect 27470 > 0 && 13735 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(27470, 13735);
expect r0 == gcd(27470, 13735);
}

// REPEAT 10 - TIME: 17.8227114 s
