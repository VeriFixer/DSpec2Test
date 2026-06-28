// Provando fibonacci
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
    decreases n-i
    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i+1)
    {
        x, y := y, x + y; //multiplas atribuições
        i := i + 1;
    }
}

// Fibonnaci
// n | Fib
// 0 | 0
// 1 | 1
// 2 | 1
// 3 | 2
// 4 | 3
// 5 | 5
// Teste da computação do Fibonnaci
// i | n | x | y | n-1
// 0 | 3 | 0 | 1 | 3
// 1 | 3 | 1 | 1 | 2
// 2 | 3 | 1 | 2 | 1
// 3 | 3 | 2 | 3 | 0
// Variante: n - 1
// Invariante: x = Fib(i)  = x sempre é o resultado do fibonnaci do valor de i
// Invariante: 0 <= i <= n = i deve ter um valor entre 0 e o valor de n
// Invariante: y = Fib(i+1) = o valor de y sempre vai ser o valor de fibonnaci mais um

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

// REPEAT 1 - TIME: 8.1763853 s

method {:test} Test6() {
var r0 := ComputeFib(101);
expect r0 == Fib(101);
}

// REPEAT 2 - TIME: 9.2625001 s

method {:test} Test7() {
var r0 := ComputeFib(102);
expect r0 == Fib(102);
}

// REPEAT 3 - TIME: 10.2316757 s

method {:test} Test8() {
var r0 := ComputeFib(103);
expect r0 == Fib(103);
}

// REPEAT 4 - TIME: 11.0289215 s

method {:test} Test9() {
var r0 := ComputeFib(104);
expect r0 == Fib(104);
}

// REPEAT 5 - TIME: 11.9637317 s

method {:test} Test10() {
var r0 := ComputeFib(105);
expect r0 == Fib(105);
}

// REPEAT 6 - TIME: 12.8042175 s

method {:test} Test11() {
var r0 := ComputeFib(106);
expect r0 == Fib(106);
}

// REPEAT 7 - TIME: 13.578696 s

method {:test} Test12() {
var r0 := ComputeFib(107);
expect r0 == Fib(107);
}

// REPEAT 8 - TIME: 14.6554425 s

method {:test} Test13() {
var r0 := ComputeFib(108);
expect r0 == Fib(108);
}

// REPEAT 9 - TIME: 15.5800638 s

method {:test} Test14() {
var r0 := ComputeFib(109);
expect r0 == Fib(109);
}

// REPEAT 10 - TIME: 16.4590624 s
