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

// REPEAT 1 - TIME: 3.1193172 s

method {:test} Test1() {
var r0 := ComputeFib(2);
expect r0 == Fib(2);
}

// REPEAT 2 - TIME: 4.5752181 s

method {:test} Test2() {
var r0 := ComputeFib(3);
expect r0 == Fib(3);
}

// REPEAT 3 - TIME: 5.5910398 s

method {:test} Test3() {
var r0 := ComputeFib(1240);
expect r0 == Fib(1240);
}

// REPEAT 4 - TIME: 6.6294772 s

method {:test} Test4() {
var r0 := ComputeFib(1241);
expect r0 == Fib(1241);
}

// REPEAT 5 - TIME: 7.6340776 s

method {:test} Test5() {
var r0 := ComputeFib(1242);
expect r0 == Fib(1242);
}

// REPEAT 6 - TIME: 8.5017057 s

method {:test} Test6() {
var r0 := ComputeFib(1243);
expect r0 == Fib(1243);
}

// REPEAT 7 - TIME: 9.4158412 s

method {:test} Test7() {
var r0 := ComputeFib(1244);
expect r0 == Fib(1244);
}

// REPEAT 8 - TIME: 10.2113404 s

method {:test} Test8() {
var r0 := ComputeFib(1245);
expect r0 == Fib(1245);
}

// REPEAT 9 - TIME: 10.9838375 s

method {:test} Test9() {
var r0 := ComputeFib(1246);
expect r0 == Fib(1246);
}

// REPEAT 10 - TIME: 11.705664 s
