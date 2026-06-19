
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

method {:test} Test23() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(101);
expect r0 == fib(101);
}
method {:test} Test24() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(101);
expect r0 == fact(101);
}
method {:test} Test25() {
expect 20270 > 0 && 10135 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20270, 10135);
expect r0 == gcd(20270, 10135);
}

// REPEAT 2 - TIME: 15.7837332 s

method {:test} Test26() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(102);
expect r0 == fib(102);
}
method {:test} Test27() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(102);
expect r0 == fact(102);
}
method {:test} Test28() {
expect 20273 > 0 && 10136 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20273, 10136);
expect r0 == gcd(20273, 10136);
}

// REPEAT 3 - TIME: 17.2493848 s

method {:test} Test29() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(103);
expect r0 == fib(103);
}
method {:test} Test30() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(103);
expect r0 == fact(103);
}
method {:test} Test31() {
expect 20275 > 0 && 10137 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20275, 10137);
expect r0 == gcd(20275, 10137);
}

// REPEAT 4 - TIME: 18.73521 s

method {:test} Test32() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(104);
expect r0 == fib(104);
}
method {:test} Test33() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(104);
expect r0 == fact(104);
}
method {:test} Test34() {
expect 20277 > 0 && 10138 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20277, 10138);
expect r0 == gcd(20277, 10138);
}

// REPEAT 5 - TIME: 20.1251214 s

method {:test} Test35() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(105);
expect r0 == fib(105);
}
method {:test} Test36() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(105);
expect r0 == fact(105);
}
method {:test} Test37() {
expect 20279 > 0 && 10139 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20279, 10139);
expect r0 == gcd(20279, 10139);
}

// REPEAT 6 - TIME: 21.5577428 s

method {:test} Test38() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(106);
expect r0 == fib(106);
}
method {:test} Test39() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(106);
expect r0 == fact(106);
}
method {:test} Test40() {
expect 20281 > 0 && 10140 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(20281, 10140);
expect r0 == gcd(20281, 10140);
}

// REPEAT 7 - TIME: 23.0228702 s

method {:test} Test41() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(107);
expect r0 == fib(107);
}
method {:test} Test42() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(107);
expect r0 == fact(107);
}
method {:test} Test43() {
expect 23874 > 0 && 11937 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23874, 11937);
expect r0 == gcd(23874, 11937);
}

// REPEAT 8 - TIME: 24.3136237 s

method {:test} Test44() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(108);
expect r0 == fib(108);
}
method {:test} Test45() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(108);
expect r0 == fact(108);
}
method {:test} Test46() {
expect 23876 > 0 && 11938 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23876, 11938);
expect r0 == gcd(23876, 11938);
}

// REPEAT 9 - TIME: 25.6944103 s

method {:test} Test47() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(109);
expect r0 == fib(109);
}
method {:test} Test48() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(109);
expect r0 == fact(109);
}
method {:test} Test49() {
expect 23879 > 0 && 11939 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(23879, 11939);
expect r0 == gcd(23879, 11939);
}

// REPEAT 10 - TIME: 27.0905456 s
