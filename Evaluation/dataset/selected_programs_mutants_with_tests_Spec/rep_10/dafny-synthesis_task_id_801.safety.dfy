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
var r0 := CountEqualNumbers(60, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 60 == 60 && 60 == 60;
expect r0 == 2 <==> (60 == 60 && 60 != 60) || (60 != 60 && 60 == 60) || (60 == 60 && 60 != 60);
expect r0 == 1 <==> 60 != 60 && 60 != 60 && 60 != 60;
}
method {:test} Test46() {
var r0 := CountEqualNumbers(61, 60, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 60 && 60 == 60;
expect r0 == 2 <==> (61 == 60 && 60 != 60) || (61 != 60 && 60 == 60) || (61 == 60 && 60 != 60);
expect r0 == 1 <==> 61 != 60 && 60 != 60 && 61 != 60;
}
method {:test} Test47() {
var r0 := CountEqualNumbers(61, 60, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 61 == 60 && 60 == 61;
expect r0 == 2 <==> (61 == 60 && 60 != 61) || (61 != 60 && 60 == 61) || (61 == 61 && 60 != 61);
expect r0 == 1 <==> 61 != 60 && 60 != 61 && 61 != 61;
}
method {:test} Test48() {
var r0 := CountEqualNumbers(62, 61, 60);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 62 == 61 && 61 == 60;
expect r0 == 2 <==> (62 == 61 && 61 != 60) || (62 != 61 && 61 == 60) || (62 == 60 && 61 != 60);
expect r0 == 1 <==> 62 != 61 && 61 != 60 && 62 != 60;
}
method {:test} Test49() {
var r0 := CountEqualNumbers(60, 60, 61);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 60 == 60 && 60 == 61;
expect r0 == 2 <==> (60 == 60 && 60 != 61) || (60 != 60 && 60 == 61) || (60 == 61 && 60 != 61);
expect r0 == 1 <==> 60 != 60 && 60 != 61 && 60 != 61;
}

// REPEAT 10 - TIME: 145.3479297 s
