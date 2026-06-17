
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
expect 1 > 0 && 452 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(1, 452);
expect r0 == gcd(1, 452);
}

// REPEAT 1 - TIME: 19.6313244 s

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
expect 2 > 0 && 453 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(2, 453);
expect r0 == gcd(2, 453);
}

// REPEAT 2 - TIME: 35.2642888 s

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
expect 3 > 0 && 454 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(3, 454);
expect r0 == gcd(3, 454);
}

// REPEAT 3 - TIME: 53.0431402 s

method {:test} Test9() {
expect 539 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(539);
expect r0 == fib(539);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(5);
expect r0 == fact(5);
}
method {:test} Test11() {
expect 7947 > 0 && 15894 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7947, 15894);
expect r0 == gcd(7947, 15894);
}

// REPEAT 4 - TIME: 70.8364524 s

method {:test} Test12() {
expect 540 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(540);
expect r0 == fib(540);
}
method {:test} Test13() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(6);
expect r0 == fact(6);
}
method {:test} Test14() {
expect 7948 > 0 && 15896 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7948, 15896);
expect r0 == gcd(7948, 15896);
}

// REPEAT 5 - TIME: 90.5174067 s

method {:test} Test15() {
expect 541 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(541);
expect r0 == fib(541);
}
method {:test} Test16() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(7);
expect r0 == fact(7);
}
method {:test} Test17() {
expect 7949 > 0 && 15898 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7949, 15898);
expect r0 == gcd(7949, 15898);
}

// REPEAT 6 - TIME: 109.7553135 s

method {:test} Test18() {
expect 542 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(542);
expect r0 == fib(542);
}
method {:test} Test19() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(8);
expect r0 == fact(8);
}
method {:test} Test20() {
expect 7950 > 0 && 15900 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7950, 15900);
expect r0 == gcd(7950, 15900);
}

// REPEAT 7 - TIME: 131.5025772 s

method {:test} Test21() {
expect 543 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(543);
expect r0 == fib(543);
}
method {:test} Test22() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(9);
expect r0 == fact(9);
}
method {:test} Test23() {
expect 7951 > 0 && 23622 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7951, 23622);
expect r0 == gcd(7951, 23622);
}

// REPEAT 8 - TIME: 154.9001729 s

method {:test} Test24() {
expect 544 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(544);
expect r0 == fib(544);
}
method {:test} Test25() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(10);
expect r0 == fact(10);
}
method {:test} Test26() {
expect 7952 > 0 && 23623 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(7952, 23623);
expect r0 == gcd(7952, 23623);
}

// REPEAT 9 - TIME: 179.5411667 s

method {:test} Test27() {
expect 545 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := fibIter(545);
expect r0 == fib(545);
}
method {:test} Test28() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := factIter(11);
expect r0 == fact(11);
}
method {:test} Test29() {
expect 19531 > 0 && 39062 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := gcdI(19531, 39062);
expect r0 == gcd(19531, 39062);
}

// REPEAT 10 - TIME: 205.9602527 s
