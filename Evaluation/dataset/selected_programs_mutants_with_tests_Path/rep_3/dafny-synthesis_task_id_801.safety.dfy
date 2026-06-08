method {:testEntry} CountEqualNumbers(a: int, b: int, c: int) returns (count: int)
    ensures count >= 0 && count <= 3
    ensures (count == 3) <==> (a == b && b == c)
    ensures (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c))
    ensures (count == 1) <==> (a != b && b != c && a != c)
{
    count := 1;
    if (a == b) {
        count := count + 1;
    }
    if (a == c) {
        count := count + 1;
    }
    if (a != b && b == c) {
        count := count + 1;
    }
}

method {:test} Test10() {
var r0 := CountEqualNumbers(30, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 30 && 30 == 30;
expect r0 == 2 <==> (30 == 30 && 30 != 30) || (30 != 30 && 30 == 30) || (30 == 30 && 30 != 30);
expect r0 == 1 <==> 30 != 30 && 30 != 30 && 30 != 30;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(31, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 31 && 31 == 30;
expect r0 == 2 <==> (31 == 31 && 31 != 30) || (31 != 31 && 31 == 30) || (31 == 30 && 31 != 30);
expect r0 == 1 <==> 31 != 31 && 31 != 30 && 31 != 30;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(30, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 30 == 31 && 31 == 30;
expect r0 == 2 <==> (30 == 31 && 31 != 30) || (30 != 31 && 31 == 30) || (30 == 30 && 31 != 30);
expect r0 == 1 <==> 30 != 31 && 31 != 30 && 30 != 30;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(31, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 30 && 30 == 30;
expect r0 == 2 <==> (31 == 30 && 30 != 30) || (31 != 30 && 30 == 30) || (31 == 30 && 30 != 30);
expect r0 == 1 <==> 31 != 30 && 30 != 30 && 31 != 30;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(32, 31, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 32 == 31 && 31 == 30;
expect r0 == 2 <==> (32 == 31 && 31 != 30) || (32 != 31 && 31 == 30) || (32 == 30 && 31 != 30);
expect r0 == 1 <==> 32 != 31 && 31 != 30 && 32 != 30;
}

// REPEAT 3 - TIME: 22.076486 s
