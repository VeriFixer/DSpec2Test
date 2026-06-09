function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

method {:testEntry} Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 1;
    while i <= n
        decreases n-i //variante
        invariant 1 <= i <= n+1 //invariante
        invariant f == Fat(i-1) //invariante
    {
        f := f * i;
        i := i + 1;
    }
    return f;
}

// i | n | variante
// 1 | 3 | 2
// 2 | 3 | 1
// 3 | 3 | 0
// 4 | 3 | -1
// variante = n - i
// então é usado o decreases n-1

method {:test} Test0() {
var r0 := Fatorial(2);
expect r0 == Fat(2);
}
method {:test} Test1() {
var r0 := Fatorial(100);
expect r0 == Fat(100);
}

// REPEAT 1 - TIME: 5.2205776 s

method {:test} Test6() {
var r0 := Fatorial(101);
expect r0 == Fat(101);
}

// REPEAT 2 - TIME: 6.1037527 s

method {:test} Test7() {
var r0 := Fatorial(102);
expect r0 == Fat(102);
}

// REPEAT 3 - TIME: 6.8405065 s

method {:test} Test8() {
var r0 := Fatorial(103);
expect r0 == Fat(103);
}

// REPEAT 4 - TIME: 7.5191783 s

method {:test} Test9() {
var r0 := Fatorial(104);
expect r0 == Fat(104);
}

// REPEAT 5 - TIME: 8.1719221 s

method {:test} Test10() {
var r0 := Fatorial(105);
expect r0 == Fat(105);
}

// REPEAT 6 - TIME: 8.8263746 s

method {:test} Test11() {
var r0 := Fatorial(106);
expect r0 == Fat(106);
}

// REPEAT 7 - TIME: 9.4729043 s

method {:test} Test12() {
var r0 := Fatorial(107);
expect r0 == Fat(107);
}

// REPEAT 8 - TIME: 10.12362 s

method {:test} Test13() {
var r0 := Fatorial(108);
expect r0 == Fat(108);
}

// REPEAT 9 - TIME: 10.6928115 s

method {:test} Test14() {
var r0 := Fatorial(109);
expect r0 == Fat(109);
}

// REPEAT 10 - TIME: 11.4824572 s
