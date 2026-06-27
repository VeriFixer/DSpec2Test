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

// REPEAT 1 - TIME: 2.811274 s

method {:test} Test1() {
var r0 := Mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 3.8305919 s

method {:test} Test2() {
var r0 := Mult(2, 2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 4.79454 s

method {:test} Test3() {
var r0 := Mult(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 5.783024 s

method {:test} Test4() {
var r0 := Mult(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 6.7293169 s

method {:test} Test5() {
var r0 := Mult(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 7.5326293 s

method {:test} Test6() {
var r0 := Mult(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 8.3196266 s

method {:test} Test7() {
var r0 := Mult(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 9.0417742 s

method {:test} Test8() {
var r0 := Mult(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 9.6937455 s

method {:test} Test9() {
var r0 := Mult(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 10.3797175 s
