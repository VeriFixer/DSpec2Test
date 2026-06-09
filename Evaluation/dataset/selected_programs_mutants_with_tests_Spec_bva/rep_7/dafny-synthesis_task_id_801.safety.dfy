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

method {:test} Test75() {
var r0 := CountEqualNumbers(49, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 49;
expect r0 == 2 <==> (49 == 49 && 49 != 49) || (49 != 49 && 49 == 49) || (49 == 49 && 49 != 49);
expect r0 == 1 <==> 49 != 49 && 49 != 49 && 49 != 49;
}
method {:test} Test76() {
var r0 := CountEqualNumbers(50, 49, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 49;
expect r0 == 2 <==> (50 == 49 && 49 != 49) || (50 != 49 && 49 == 49) || (50 == 49 && 49 != 49);
expect r0 == 1 <==> 50 != 49 && 49 != 49 && 50 != 49;
}
method {:test} Test77() {
var r0 := CountEqualNumbers(50, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 50;
expect r0 == 2 <==> (50 == 49 && 49 != 50) || (50 != 49 && 49 == 50) || (50 == 50 && 49 != 50);
expect r0 == 1 <==> 50 != 49 && 49 != 50 && 50 != 50;
}
method {:test} Test78() {
var r0 := CountEqualNumbers(50, 49, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 49 && 49 == 51;
expect r0 == 2 <==> (50 == 49 && 49 != 51) || (50 != 49 && 49 == 51) || (50 == 51 && 49 != 51);
expect r0 == 1 <==> 50 != 49 && 49 != 51 && 50 != 51;
}
method {:test} Test79() {
var r0 := CountEqualNumbers(49, 49, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 49 && 49 == 50;
expect r0 == 2 <==> (49 == 49 && 49 != 50) || (49 != 49 && 49 == 50) || (49 == 50 && 49 != 50);
expect r0 == 1 <==> 49 != 49 && 49 != 50 && 49 != 50;
}

// REPEAT 7 - TIME: 234.7231327 s
