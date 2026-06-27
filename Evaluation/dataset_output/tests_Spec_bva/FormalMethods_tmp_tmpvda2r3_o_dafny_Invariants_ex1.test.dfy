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
method {:test} Test1() {
var r0 := Mult(100, 38);
expect r0 == 100 * 38;
}
method {:test} Test2() {
var r0 := Mult(38, 100);
expect r0 == 38 * 100;
}
method {:test} Test4() {
var r0 := Mult(1, 100);
expect r0 == 1 * 100;
}

// REPEAT 1 - TIME: 6.3127543 s

method {:test} Test7() {
var r0 := Mult(101, 101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 7.0652173 s

method {:test} Test8() {
var r0 := Mult(102, 102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 7.8677691 s

method {:test} Test9() {
var r0 := Mult(103, 103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 8.5775035 s

method {:test} Test10() {
var r0 := Mult(104, 104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 9.4164696 s

method {:test} Test11() {
var r0 := Mult(105, 105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 10.0910161 s

method {:test} Test12() {
var r0 := Mult(106, 106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 10.7470947 s

method {:test} Test13() {
var r0 := Mult(107, 107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 11.4688855 s

method {:test} Test14() {
var r0 := Mult(108, 108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 12.182808 s

method {:test} Test15() {
var r0 := Mult(109, 109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 12.7708602 s
