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

method {:test} Test30() {
var r0 := CountEqualNumbers(48, 48, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 48 == 48 && 48 == 48;
expect r0 == 2 <==> (48 == 48 && 48 != 48) || (48 != 48 && 48 == 48) || (48 == 48 && 48 != 48);
expect r0 == 1 <==> 48 != 48 && 48 != 48 && 48 != 48;
}
method {:test} Test31() {
var r0 := CountEqualNumbers(50, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 51 && 51 == 51;
expect r0 == 2 <==> (50 == 51 && 51 != 51) || (50 != 51 && 51 == 51) || (50 == 51 && 51 != 51);
expect r0 == 1 <==> 50 != 51 && 51 != 51 && 50 != 51;
}
method {:test} Test32() {
var r0 := CountEqualNumbers(49, 48, 49);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 49;
expect r0 == 2 <==> (49 == 48 && 48 != 49) || (49 != 48 && 48 == 49) || (49 == 49 && 48 != 49);
expect r0 == 1 <==> 49 != 48 && 48 != 49 && 49 != 49;
}
method {:test} Test33() {
var r0 := CountEqualNumbers(49, 48, 50);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 49 == 48 && 48 == 50;
expect r0 == 2 <==> (49 == 48 && 48 != 50) || (49 != 48 && 48 == 50) || (49 == 50 && 48 != 50);
expect r0 == 1 <==> 49 != 48 && 48 != 50 && 49 != 50;
}
method {:test} Test34() {
var r0 := CountEqualNumbers(50, 50, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 50 == 50 && 50 == 51;
expect r0 == 2 <==> (50 == 50 && 50 != 51) || (50 != 50 && 50 == 51) || (50 == 51 && 50 != 51);
expect r0 == 1 <==> 50 != 50 && 50 != 51 && 50 != 51;
}

// REPEAT 7 - TIME: 98.8314062 s
