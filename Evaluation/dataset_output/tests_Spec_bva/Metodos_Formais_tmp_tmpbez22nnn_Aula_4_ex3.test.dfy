function Fib(n:nat):nat
{
    if n < 2
    then n
    else Fib(n-2) + Fib(n-1)
}

method {:testEntry} ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i+1)
    {
        x, y := y, x + y;
        i := i + 1;
    }
}

method {:testEntry} Teste()
{
    var n := 3;
    var f := ComputeFib(n);
    assert f == 2;
}

method {:test} Test0() {
var r0 := ComputeFib(1);
expect r0 == Fib(1);
}
method {:test} Test1() {
var r0 := ComputeFib(100);
expect r0 == Fib(100);
}
method {:test} Test3() {
var r0 := ComputeFib(3);
expect r0 == Fib(3);
}
method {:test} Test6() {
Teste();
}

// REPEAT 1 - TIME: 7.818596 s

method {:test} Test9() {
var r0 := ComputeFib(101);
expect r0 == Fib(101);
}

// REPEAT 2 - TIME: 8.5394508 s

method {:test} Test10() {
var r0 := ComputeFib(102);
expect r0 == Fib(102);
}

// REPEAT 3 - TIME: 9.288569 s

method {:test} Test11() {
var r0 := ComputeFib(103);
expect r0 == Fib(103);
}

// REPEAT 4 - TIME: 9.989459 s

method {:test} Test12() {
var r0 := ComputeFib(104);
expect r0 == Fib(104);
}

// REPEAT 5 - TIME: 10.6129961 s

method {:test} Test13() {
var r0 := ComputeFib(105);
expect r0 == Fib(105);
}

// REPEAT 6 - TIME: 11.2855482 s

method {:test} Test14() {
var r0 := ComputeFib(106);
expect r0 == Fib(106);
}

// REPEAT 7 - TIME: 11.9714 s

method {:test} Test15() {
var r0 := ComputeFib(107);
expect r0 == Fib(107);
}

// REPEAT 8 - TIME: 12.6090757 s

method {:test} Test16() {
var r0 := ComputeFib(108);
expect r0 == Fib(108);
}

// REPEAT 9 - TIME: 13.2951432 s

method {:test} Test17() {
var r0 := ComputeFib(109);
expect r0 == Fib(109);
}

// REPEAT 10 - TIME: 13.9789647 s
