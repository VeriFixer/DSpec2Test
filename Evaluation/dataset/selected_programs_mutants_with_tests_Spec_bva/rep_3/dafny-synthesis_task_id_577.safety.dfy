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

method {:test} Test8() {
expect 62836 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62836);
expect r0 == Factorial(62836 % 10);
}

// REPEAT 3 - TIME: 8.0935847 s
