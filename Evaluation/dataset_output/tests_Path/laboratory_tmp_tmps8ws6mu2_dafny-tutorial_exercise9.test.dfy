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

// REPEAT 1 - TIME: 4.6932282 s

method {:test} Test1() {
var r0 := ComputeFib(1801);
expect r0 == fib(1801);
}

// REPEAT 2 - TIME: 7.7288102 s

method {:test} Test2() {
var r0 := ComputeFib(1802);
expect r0 == fib(1802);
}

// REPEAT 3 - TIME: 10.0018109 s

method {:test} Test3() {
var r0 := ComputeFib(1803);
expect r0 == fib(1803);
}

// REPEAT 4 - TIME: 12.2941583 s

method {:test} Test4() {
var r0 := ComputeFib(1804);
expect r0 == fib(1804);
}

// REPEAT 5 - TIME: 14.7223742 s

method {:test} Test5() {
var r0 := ComputeFib(1805);
expect r0 == fib(1805);
}

// REPEAT 6 - TIME: 17.1097267 s

method {:test} Test6() {
var r0 := ComputeFib(1806);
expect r0 == fib(1806);
}

// REPEAT 7 - TIME: 19.7506543 s

method {:test} Test7() {
var r0 := ComputeFib(1807);
expect r0 == fib(1807);
}

// REPEAT 8 - TIME: 22.4490417 s

method {:test} Test8() {
var r0 := ComputeFib(1808);
expect r0 == fib(1808);
}

// REPEAT 9 - TIME: 24.9668457 s

method {:test} Test9() {
var r0 := ComputeFib(1809);
expect r0 == fib(1809);
}

// REPEAT 10 - TIME: 27.5208355 s
