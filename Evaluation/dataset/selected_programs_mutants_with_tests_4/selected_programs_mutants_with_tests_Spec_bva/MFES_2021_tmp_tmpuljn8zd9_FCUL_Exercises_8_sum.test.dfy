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

method {:test} Test0() {
var r0 := sum(0);
expect r0 == calcSum(0 + 1);
}
method {:test} Test1() {
var r0 := sum(100);
expect r0 == calcSum(100 + 1);
}
method {:test} Test5() {
var r0 := sum(101);
expect r0 == calcSum(101 + 1);
}
method {:test} Test6() {
var r0 := sum(102);
expect r0 == calcSum(102 + 1);
}
method {:test} Test7() {
var r0 := sum(103);
expect r0 == calcSum(103 + 1);
}
