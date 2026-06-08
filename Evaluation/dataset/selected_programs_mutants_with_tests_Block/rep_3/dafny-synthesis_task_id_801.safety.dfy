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

method {:test} Test5() {
var r0 := CountEqualNumbers(29, 30, 30);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 30 && 30 == 30;
expect r0 == 2 <==> (29 == 30 && 30 != 30) || (29 != 30 && 30 == 30) || (29 == 30 && 30 != 30);
expect r0 == 1 <==> 29 != 30 && 30 != 30 && 29 != 30;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(31, 31, 31);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 31 == 31 && 31 == 31;
expect r0 == 2 <==> (31 == 31 && 31 != 31) || (31 != 31 && 31 == 31) || (31 == 31 && 31 != 31);
expect r0 == 1 <==> 31 != 31 && 31 != 31 && 31 != 31;
}

// REPEAT 3 - TIME: 5.5847218 s
