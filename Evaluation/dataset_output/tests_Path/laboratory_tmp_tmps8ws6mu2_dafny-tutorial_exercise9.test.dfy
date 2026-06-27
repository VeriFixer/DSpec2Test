function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
                    fib(n - 1) + fib(n - 2)
}

method {:testEntry} ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
{
    // Change the method {:testEntry} body to instead use c as described.
    // You will need to change both the initialization and the loop.
    var i: int := 0;
        b := 0;
    var c := 1;
    while i < n
        invariant 0 <= i <= n
        invariant b == fib(i)
        invariant c == fib(i + 1)
    {
        b, c := c, c + b;
        i := i + 1;
    }
}

method {:test} Test0() {
var r0 := ComputeFib(1800);
expect r0 == fib(1800);
}

// REPEAT 1 - TIME: 3.9222245 s

method {:test} Test1() {
var r0 := ComputeFib(1801);
expect r0 == fib(1801);
}

// REPEAT 2 - TIME: 6.2149926 s

method {:test} Test2() {
var r0 := ComputeFib(1802);
expect r0 == fib(1802);
}

// REPEAT 3 - TIME: 8.2848795 s

method {:test} Test3() {
var r0 := ComputeFib(1803);
expect r0 == fib(1803);
}

// REPEAT 4 - TIME: 9.9853942 s

method {:test} Test4() {
var r0 := ComputeFib(1804);
expect r0 == fib(1804);
}

// REPEAT 5 - TIME: 11.8465712 s

method {:test} Test5() {
var r0 := ComputeFib(1805);
expect r0 == fib(1805);
}

// REPEAT 6 - TIME: 13.7830507 s

method {:test} Test6() {
var r0 := ComputeFib(1806);
expect r0 == fib(1806);
}

// REPEAT 7 - TIME: 15.7476854 s

method {:test} Test7() {
var r0 := ComputeFib(1807);
expect r0 == fib(1807);
}

// REPEAT 8 - TIME: 17.6620604 s

method {:test} Test8() {
var r0 := ComputeFib(1808);
expect r0 == fib(1808);
}

// REPEAT 9 - TIME: 19.635297 s

method {:test} Test9() {
var r0 := ComputeFib(1809);
expect r0 == fib(1809);
}

// REPEAT 10 - TIME: 21.7407022 s
