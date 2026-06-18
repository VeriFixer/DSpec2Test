function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

method {:testEntry} factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{
    var i := 1;
    res := 1;
    while i < n + 1 
        invariant 0 < i <= n + 1
        invariant res == fact(i - 1) // result satisfies postcondition for every iteration, verification fails without this
    {
        res := i * res;
        i := i + 1;
    }
}

method {:test} Test0() {
var r0 := factorial(1);
expect r0 == fact(1);
}

// REPEAT 1 - TIME: 2.1006334 s

method {:test} Test1() {
var r0 := factorial(2);
expect r0 == fact(2);
}

// REPEAT 2 - TIME: 2.7609713 s

method {:test} Test2() {
var r0 := factorial(3);
expect r0 == fact(3);
}

// REPEAT 3 - TIME: 3.4694103 s

method {:test} Test3() {
var r0 := factorial(4);
expect r0 == fact(4);
}

// REPEAT 4 - TIME: 4.1949397 s

method {:test} Test4() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 5 - TIME: 4.950157 s

method {:test} Test5() {
var r0 := factorial(6);
expect r0 == fact(6);
}

// REPEAT 6 - TIME: 5.7537771 s

method {:test} Test6() {
var r0 := factorial(7);
expect r0 == fact(7);
}

// REPEAT 7 - TIME: 6.4982765 s

method {:test} Test7() {
var r0 := factorial(8);
expect r0 == fact(8);
}

// REPEAT 8 - TIME: 7.0437256 s

method {:test} Test8() {
var r0 := factorial(9);
expect r0 == fact(9);
}

// REPEAT 9 - TIME: 7.7578967 s

method {:test} Test9() {
var r0 := factorial(10);
expect r0 == fact(10);
}

// REPEAT 10 - TIME: 8.2883183 s
