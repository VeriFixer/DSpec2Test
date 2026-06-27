function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x, y-1)
}

method {:testEntry} Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
    r := 1;
    var b := x;
    var e := y;
    while e > 0
    invariant Potencia(b,e) * r == Potencia(x,y)
    {
        r := r * b;
        e := e - 1;
    }

    return r;
}
/*
Inv = 
Pot(2,3)
Teste de mesa
x   y   b   e   r           Inv --> b^e * r = x^y
2   3   2   3   1           2^3 * 2^0 = 2^3
2   3   2   2   1*2         2^2 * 2^1 = 2^3
2   3   2   1   1*2*2       2^1 * 2^2 = 2^3
2   3   2   0   1*2*2*2     2^0 * 2^3 = 2^3
*/

method {:test} Test0() {
var r0 := Pot(0, 2);
expect r0 == Potencia(0, 2);
}

// REPEAT 1 - TIME: 6.6400702 s

method {:test} Test1() {
var r0 := Pot(1, 3);
expect r0 == Potencia(1, 3);
}

// REPEAT 2 - TIME: 10.5141613 s

method {:test} Test2() {
var r0 := Pot(2, 4);
expect r0 == Potencia(2, 4);
}

// REPEAT 3 - TIME: 13.4614869 s

method {:test} Test3() {
var r0 := Pot(3, 5);
expect r0 == Potencia(3, 5);
}

// REPEAT 4 - TIME: 16.7240034 s

method {:test} Test4() {
var r0 := Pot(4, 6);
expect r0 == Potencia(4, 6);
}

// REPEAT 5 - TIME: 19.678708 s

method {:test} Test5() {
var r0 := Pot(5, 7);
expect r0 == Potencia(5, 7);
}

// REPEAT 6 - TIME: 22.765773 s

method {:test} Test6() {
var r0 := Pot(6, 8);
expect r0 == Potencia(6, 8);
}

// REPEAT 7 - TIME: 25.9605236 s

method {:test} Test7() {
var r0 := Pot(7, 9);
expect r0 == Potencia(7, 9);
}

// REPEAT 8 - TIME: 29.4799772 s

method {:test} Test8() {
var r0 := Pot(8, 10);
expect r0 == Potencia(8, 10);
}

// REPEAT 9 - TIME: 32.8757476 s

method {:test} Test9() {
var r0 := Pot(9, 11);
expect r0 == Potencia(9, 11);
}

// REPEAT 10 - TIME: 36.1511882 s
