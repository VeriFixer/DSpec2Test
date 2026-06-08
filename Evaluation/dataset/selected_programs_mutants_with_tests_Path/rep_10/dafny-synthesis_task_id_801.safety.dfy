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

method {:test} Test45() {
var r0 := CountEqualNumbers(51, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 51 && 51 == 51;
expect r0 == 2 <==> (51 == 51 && 51 != 51) || (51 != 51 && 51 == 51) || (51 == 51 && 51 != 51);
expect r0 == 1 <==> 51 != 51 && 51 != 51 && 51 != 51;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(52, 52, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 51;
expect r0 == 2 <==> (52 == 52 && 52 != 51) || (52 != 52 && 52 == 51) || (52 == 51 && 52 != 51);
expect r0 == 1 <==> 52 != 52 && 52 != 51 && 52 != 51;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(51, 52, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 51 == 52 && 52 == 51;
expect r0 == 2 <==> (51 == 52 && 52 != 51) || (51 != 52 && 52 == 51) || (51 == 51 && 52 != 51);
expect r0 == 1 <==> 51 != 52 && 52 != 51 && 51 != 51;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(52, 51, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 51 && 51 == 51;
expect r0 == 2 <==> (52 == 51 && 51 != 51) || (52 != 51 && 51 == 51) || (52 == 51 && 51 != 51);
expect r0 == 1 <==> 52 != 51 && 51 != 51 && 52 != 51;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(53, 52, 51);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 51;
expect r0 == 2 <==> (53 == 52 && 52 != 51) || (53 != 52 && 52 == 51) || (53 == 51 && 52 != 51);
expect r0 == 1 <==> 53 != 52 && 52 != 51 && 53 != 51;
}

// REPEAT 10 - TIME: 75.9785549 s
