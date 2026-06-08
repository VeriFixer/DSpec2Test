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

// REPEAT 1 - TIME: 6.2181962 s

method {:test} Test1() {
var r0 := Fatorial(3);
expect r0 == Fat(3);
}

// REPEAT 2 - TIME: 9.659905 s

method {:test} Test2() {
var r0 := Fatorial(4);
expect r0 == Fat(4);
}

// REPEAT 3 - TIME: 12.8416944 s

method {:test} Test3() {
var r0 := Fatorial(5);
expect r0 == Fat(5);
}

// REPEAT 4 - TIME: 16.046995 s

method {:test} Test4() {
var r0 := Fatorial(6);
expect r0 == Fat(6);
}

// REPEAT 5 - TIME: 18.8499055 s

method {:test} Test5() {
var r0 := Fatorial(7);
expect r0 == Fat(7);
}

// REPEAT 6 - TIME: 21.4636795 s

method {:test} Test6() {
var r0 := Fatorial(8);
expect r0 == Fat(8);
}

// REPEAT 7 - TIME: 23.9026296 s

method {:test} Test7() {
var r0 := Fatorial(9);
expect r0 == Fat(9);
}

// REPEAT 8 - TIME: 26.8952694 s

method {:test} Test8() {
var r0 := Fatorial(10);
expect r0 == Fat(10);
}

// REPEAT 9 - TIME: 29.9200652 s

method {:test} Test9() {
var r0 := Fatorial(11);
expect r0 == Fat(11);
}

// REPEAT 10 - TIME: 33.2880277 s
