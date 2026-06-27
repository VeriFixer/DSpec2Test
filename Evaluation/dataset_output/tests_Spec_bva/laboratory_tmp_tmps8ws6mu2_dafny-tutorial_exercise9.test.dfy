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
var r0 := ComputeFib(1);
expect r0 == fib(1);
}
method {:test} Test1() {
var r0 := ComputeFib(100);
expect r0 == fib(100);
}
method {:test} Test3() {
var r0 := ComputeFib(3);
expect r0 == fib(3);
}
method {:test} Test4() {
var r0 := ComputeFib(2441);
expect r0 == fib(2441);
}

// REPEAT 1 - TIME: 5.961287 s

method {:test} Test6() {
var r0 := ComputeFib(2442);
expect r0 == fib(2442);
}

// REPEAT 2 - TIME: 6.9872049 s

method {:test} Test7() {
var r0 := ComputeFib(2443);
expect r0 == fib(2443);
}

// REPEAT 3 - TIME: 7.9093795 s

method {:test} Test8() {
var r0 := ComputeFib(2444);
expect r0 == fib(2444);
}

// REPEAT 4 - TIME: 8.7201791 s

method {:test} Test9() {
var r0 := ComputeFib(2445);
expect r0 == fib(2445);
}

// REPEAT 5 - TIME: 9.3705902 s

method {:test} Test10() {
var r0 := ComputeFib(2446);
expect r0 == fib(2446);
}

// REPEAT 6 - TIME: 9.9837823 s

method {:test} Test11() {
var r0 := ComputeFib(2447);
expect r0 == fib(2447);
}

// REPEAT 7 - TIME: 10.5510549 s

method {:test} Test12() {
var r0 := ComputeFib(2448);
expect r0 == fib(2448);
}

// REPEAT 8 - TIME: 11.1309196 s

method {:test} Test13() {
var r0 := ComputeFib(2449);
expect r0 == fib(2449);
}

// REPEAT 9 - TIME: 11.6299401 s

method {:test} Test14() {
var r0 := ComputeFib(2450);
expect r0 == fib(2450);
}

// REPEAT 10 - TIME: 12.1487692 s
