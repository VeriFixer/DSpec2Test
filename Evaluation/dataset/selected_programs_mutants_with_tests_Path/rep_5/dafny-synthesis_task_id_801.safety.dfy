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

method {:test} Test20() {
var r0 := CountEqualNumbers(36, 36, 36);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 36;
expect r0 == 2 <==> (36 == 36 && 36 != 36) || (36 != 36 && 36 == 36) || (36 == 36 && 36 != 36);
expect r0 == 1 <==> 36 != 36 && 36 != 36 && 36 != 36;
}
method {:test} Test21() {
var r0 := CountEqualNumbers(36, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 37;
expect r0 == 2 <==> (36 == 36 && 36 != 37) || (36 != 36 && 36 == 37) || (36 == 37 && 36 != 37);
expect r0 == 1 <==> 36 != 36 && 36 != 37 && 36 != 37;
}
method {:test} Test22() {
var r0 := CountEqualNumbers(37, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 37;
expect r0 == 2 <==> (37 == 36 && 36 != 37) || (37 != 36 && 36 == 37) || (37 == 37 && 36 != 37);
expect r0 == 1 <==> 37 != 36 && 36 != 37 && 37 != 37;
}
method {:test} Test23() {
var r0 := CountEqualNumbers(36, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 37 && 37 == 37;
expect r0 == 2 <==> (36 == 37 && 37 != 37) || (36 != 37 && 37 == 37) || (36 == 37 && 37 != 37);
expect r0 == 1 <==> 36 != 37 && 37 != 37 && 36 != 37;
}
method {:test} Test24() {
var r0 := CountEqualNumbers(37, 36, 38);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 38;
expect r0 == 2 <==> (37 == 36 && 36 != 38) || (37 != 36 && 36 == 38) || (37 == 38 && 36 != 38);
expect r0 == 1 <==> 37 != 36 && 36 != 38 && 37 != 38;
}

// REPEAT 5 - TIME: 34.8010187 s
