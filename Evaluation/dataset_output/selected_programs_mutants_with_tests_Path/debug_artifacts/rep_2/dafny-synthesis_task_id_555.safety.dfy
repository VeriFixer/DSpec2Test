method {:testEntry} DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    for i := 1 to n + 1
        invariant 0 <= i <= n + 1
        invariant sumCubes == (i - 1) * (i - 1) * i * i / 4
        invariant sumNumbers == (i - 1) * i / 2
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
    }
    diff := sumCubes - sumNumbers;
}

method {:test} Test1() {
expect 12665432492634448545274086 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DifferenceSumCubesAndSumNumbers(12665432492634448545274086);
expect r0 == 12665432492634448545274086 * 12665432492634448545274086 * (12665432492634448545274086 + 1) * (12665432492634448545274086 + 1) / 4 - 12665432492634448545274086 * (12665432492634448545274086 + 1) / 2;
}

// REPEAT 2 - TIME: 11.5598187 s
