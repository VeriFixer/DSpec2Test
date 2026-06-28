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

// REPEAT 1 - TIME: 9.849676 s
