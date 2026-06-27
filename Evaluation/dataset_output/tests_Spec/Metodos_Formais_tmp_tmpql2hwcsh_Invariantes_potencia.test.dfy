// Potência

// deve ser especificado a potência, porque ele não existe n dafny

// Função recursiva da potência
function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x,y-1)
}

// Quero agora implementar como uma função não recursiva
method {:testEntry} Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
    r := 1; //sempre r começa com 1
    var b := x; //base
    var e := y; //expoente

    while e > 0 
    invariant  Potencia(b,e)*r == Potencia(x,y) 
    {
        r := r * b;
        e := e - 1;
    }
    return r;
}

// Devemos sempre construir uma tabela para vermos passo a passo o processo
// POT(2,3)
// x | y | b | e | r | 
// 2 | 3 | 2 | 3 | 1 |
// 2 | 3 | 2 | 2 | 1x2     |
// 2 | 3 | 2 | 1 | 1x2x2   |
// 2 | 3 | 2 | 0 | 1x2x2x2 |
// temos que na invariante queremos a fórmula x^y
// INV ... = x^y
// vendo pelo que foi processado fica dando o seguinte
// x | y | b | e | r |  
// 2 | 3 | 2 | 3 | 1 (2^0)      | 2^3 x 2^0 = 2^3
// 2 | 3 | 2 | 2 | 1x2  (2^1)   | 2^2 x 2^1 = 2^3
// 2 | 3 | 2 | 1 | 1x2x2 (2^2)  | 2^1 x 2^2 = 2^3
// 2 | 3 | 2 | 0 | 1x2x2x2 (2^3)| 2^0 x 2^3 = 2^3
// portanto a base está sendo feito a potencia de e (usando o potencia) e multiplicado pelo valor de r
// b^e * r
// assim temos a fórmula: b^e * r = x^y
// dai utilizamos a function potencia para construir a fórmula
// Potencia(b,e)*r == Potencia(x,y)

method {:test} Test0() {
var r0 := Pot(0, 2);
expect r0 == Potencia(0, 2);
}

// REPEAT 1 - TIME: 3.0029947 s

method {:test} Test1() {
var r0 := Pot(1, 3);
expect r0 == Potencia(1, 3);
}

// REPEAT 2 - TIME: 3.9414416 s

method {:test} Test2() {
var r0 := Pot(2, 4);
expect r0 == Potencia(2, 4);
}

// REPEAT 3 - TIME: 4.9313116 s

method {:test} Test3() {
var r0 := Pot(3, 5);
expect r0 == Potencia(3, 5);
}

// REPEAT 4 - TIME: 5.89841 s

method {:test} Test4() {
var r0 := Pot(4, 6);
expect r0 == Potencia(4, 6);
}

// REPEAT 5 - TIME: 6.7332043 s

method {:test} Test5() {
var r0 := Pot(5, 7);
expect r0 == Potencia(5, 7);
}

// REPEAT 6 - TIME: 7.8124066 s

method {:test} Test6() {
var r0 := Pot(6, 8);
expect r0 == Potencia(6, 8);
}

// REPEAT 7 - TIME: 8.8829299 s

method {:test} Test7() {
var r0 := Pot(7, 9);
expect r0 == Potencia(7, 9);
}

// REPEAT 8 - TIME: 9.7833204 s

method {:test} Test8() {
var r0 := Pot(8, 10);
expect r0 == Potencia(8, 10);
}

// REPEAT 9 - TIME: 10.5956671 s

method {:test} Test9() {
var r0 := Pot(9, 11);
expect r0 == Potencia(9, 11);
}

// REPEAT 10 - TIME: 11.3108793 s
