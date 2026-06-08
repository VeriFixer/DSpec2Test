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
var r0 := factorial(2);
expect r0 == fact(2);
}

// REPEAT 1 - TIME: 6.4123278 s

method {:test} Test1() {
var r0 := factorial(3);
expect r0 == fact(3);
}

// REPEAT 2 - TIME: 10.0784365 s

method {:test} Test2() {
var r0 := factorial(4);
expect r0 == fact(4);
}

// REPEAT 3 - TIME: 12.9563376 s

method {:test} Test3() {
var r0 := factorial(5);
expect r0 == fact(5);
}

// REPEAT 4 - TIME: 16.2342412 s

method {:test} Test4() {
var r0 := factorial(8);
expect r0 == fact(8);
}

// REPEAT 5 - TIME: 20.279632 s

method {:test} Test5() {
var r0 := factorial(9);
expect r0 == fact(9);
}

// REPEAT 6 - TIME: 23.7539576 s

method {:test} Test6() {
var r0 := factorial(10);
expect r0 == fact(10);
}

// REPEAT 7 - TIME: 26.7721817 s

method {:test} Test7() {
var r0 := factorial(11);
expect r0 == fact(11);
}

// REPEAT 8 - TIME: 30.0317283 s

method {:test} Test8() {
var r0 := factorial(12);
expect r0 == fact(12);
}

// REPEAT 9 - TIME: 33.764527 s

method {:test} Test9() {
var r0 := factorial(13);
expect r0 == fact(13);
}

// REPEAT 10 - TIME: 37.1626293 s
