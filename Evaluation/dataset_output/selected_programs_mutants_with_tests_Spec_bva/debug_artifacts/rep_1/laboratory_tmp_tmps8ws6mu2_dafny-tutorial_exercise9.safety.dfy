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
