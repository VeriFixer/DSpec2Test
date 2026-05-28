function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}


method {:testEntry} SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
{
    s := 0;
    var k := 0;
    while k != n
        decreases n-k;
        invariant 0 <= k <= n;
        invariant s == sumInts(k)
        invariant s == k*(k+1)/2;
    {
        k := k+1;
        s := s+k;
    }
}

method {:test} Test0() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(2);
expect r0 == sumInts(2);
expect r0 == 2 * (2 + 1) / 2;
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(0);
expect r0 == sumInts(0);
expect r0 == 0 * (0 + 1) / 2;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(100);
expect r0 == sumInts(100);
expect r0 == 100 * (100 + 1) / 2;
}
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(101);
expect r0 == sumInts(101);
expect r0 == 101 * (101 + 1) / 2;
}
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(102);
expect r0 == sumInts(102);
expect r0 == 102 * (102 + 1) / 2;
}
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(103);
expect r0 == sumInts(103);
expect r0 == 103 * (103 + 1) / 2;
}
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(104);
expect r0 == sumInts(104);
expect r0 == 104 * (104 + 1) / 2;
}
method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(105);
expect r0 == sumInts(105);
expect r0 == 105 * (105 + 1) / 2;
}
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumIntsLoop(106);
expect r0 == sumInts(106);
expect r0 == 106 * (106 + 1) / 2;
}
