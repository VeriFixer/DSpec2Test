function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 then 1
        else n * Factorial(n-1)
    }

    method {:testEntry} FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
    {
        var lastDigit := n % 10;
        fact := Factorial(lastDigit);
    }

method {:test} Test9() {
expect 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(17);
expect r0 == Factorial(17 % 10);
}

// REPEAT 10 - TIME: 10.3765407 s
