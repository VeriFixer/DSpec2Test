method {:testEntry} Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    // Valores passados por parâmetros são imutáveis
    var m := x;
    var n := y;
    r := 0;
    // Soma sucessiva para multiplicar dois números.
    while m > 0
    invariant m*n+r == x*y
    invariant m>=0
    {
        r := r + n;
        m := m - 1;
    }
    return r; // NOT(m>0) ^ Inv ==> r = x*y
}

/*
Inv = m*n + r = x*y
Mult(5,3)
Teste de mesa
x   y   m   n   r       Inv --> m*n + r = x*y
5   3   5   3   0       5x3+0 = 5*3
5   3   4   3   3       4x3+3 = 5*3
5   3   3   3   6       3x3+6 = 5*3
5   3   2   3   9       2x3+9 = 5*3
5   3   1   3   12      1x3+12 = 5*3
5   3   0   3   15      0x3+15 = 5*3
*/

method {:test} Test0() {
var r0 := Mult(0, 0);
expect r0 == 0 * 0;
}

// REPEAT 1 - TIME: 5.4554319 s

method {:test} Test1() {
var r0 := Mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 9.3083736 s

method {:test} Test2() {
var r0 := Mult(2, 2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 12.2374039 s

method {:test} Test3() {
var r0 := Mult(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 15.019899 s

method {:test} Test4() {
var r0 := Mult(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 18.1749426 s

method {:test} Test5() {
var r0 := Mult(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 21.4909182 s

method {:test} Test6() {
var r0 := Mult(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 24.0617927 s

method {:test} Test7() {
var r0 := Mult(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 27.1811881 s

method {:test} Test8() {
var r0 := Mult(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 30.3950129 s

method {:test} Test9() {
var r0 := Mult(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 33.708005 s
