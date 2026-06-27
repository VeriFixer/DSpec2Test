// Exemplo de invariantes
// Invariante significa que o valor não muda desde a pré-condição até a pós-condição

method {:testEntry} Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    // parâmetros de entrada são imutáveis, por isso
    // é preciso a atribuir a variáveis locais para usar em blocos de códigos para mudar

    var m := x;
    var n := y;

    r := 0;
    while m > 0 
    invariant m >= 0
    invariant m*n+r == x*y
    {
        r := r + n;
        m := m -1;
    }
    return r;
}

// Teste do método para encontrar a invariante
// x | y | m | n | r
// 5 | 3 | 5 | 3 | 0
// 5 | 3 | 4 | 3 | 3
// 5 | 3 | 3 | 3 | 6
// 5 | 3 | 2 | 3 | 9
// 5 | 3 | 1 | 3 | 12
// 5 | 3 | 0 | 3 | 15

// vimos o seguinte:
// m * n + r = x * y
// 5 * 3 + 0 (15) = 5 * 3 (15)
// portanto a fórmula m*n+r == x*y é uma invariante
// mas só isso não serve, o m ele é maior ou igual a zero quando acaba o while
// por isso, também é a invariante que necessita
// com isso dizemos para o programa as alterações do m de maior ou igual a zero
// e mostramos a função encontrada que alterava o valor de m e n das variaveis criadas

// SE OS ALGORITMOS TIVEREM REPETIÇÃO OU RECURSÃO, DEVEM SER MOSTRADOS QUAIS SÃO AS INVARIANTES
// OU SEJA, OS VALORES QUE NÃO ESTÃO SENDO MUDADOS E COLOCAR A FÓRMULA DELE COMO ACIMA

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

// REPEAT 1 - TIME: 6.6040178 s

method {:test} Test7() {
var r0 := Mult(101, 101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 7.5587753 s

method {:test} Test8() {
var r0 := Mult(102, 102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 8.3009854 s

method {:test} Test9() {
var r0 := Mult(103, 103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 9.071473 s

method {:test} Test10() {
var r0 := Mult(104, 104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 9.7982103 s

method {:test} Test11() {
var r0 := Mult(105, 105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 10.4516056 s

method {:test} Test12() {
var r0 := Mult(106, 106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 11.1022361 s

method {:test} Test13() {
var r0 := Mult(107, 107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 11.6862746 s

method {:test} Test14() {
var r0 := Mult(108, 108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 12.2490006 s

method {:test} Test15() {
var r0 := Mult(109, 109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 12.8464308 s
