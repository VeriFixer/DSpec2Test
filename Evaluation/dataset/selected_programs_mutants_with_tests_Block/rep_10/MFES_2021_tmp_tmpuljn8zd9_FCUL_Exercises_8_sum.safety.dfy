function calcSum(n: nat) : nat 
{   
    n * (n - 1) / 2
}

method {:testEntry} sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
{
    s := 0;
    var i := 0;
    while i < n 
        decreases n - i
        invariant 0 <= i <= n
        invariant s == calcSum(i + 1)
    {
        i := i + 1;
        s := s + i;
    }
}

method {:test} Test9() {
var r0 := sum(10);
expect r0 == calcSum(10 + 1);
}

// REPEAT 10 - TIME: 7.9211467 s
