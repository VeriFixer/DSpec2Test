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

method {:test} Test11() {
var r0 := CountEqualNumbers(37, 38, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 38 && 38 == 38;
expect r0 == 2 <==> (37 == 38 && 38 != 38) || (37 != 38 && 38 == 38) || (37 == 38 && 38 != 38);
expect r0 == 1 <==> 37 != 38 && 38 != 38 && 37 != 38;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(37, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 37;
expect r0 == 2 <==> (37 == 37 && 37 != 37) || (37 != 37 && 37 == 37) || (37 == 37 && 37 != 37);
expect r0 == 1 <==> 37 != 37 && 37 != 37 && 37 != 37;
}

// REPEAT 6 - TIME: 9.6232544 s
