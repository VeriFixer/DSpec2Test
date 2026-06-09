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

method {:test} Test90() {
var r0 := CountEqualNumbers(58, 58, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 58;
expect r0 == 2 <==> (58 == 58 && 58 != 58) || (58 != 58 && 58 == 58) || (58 == 58 && 58 != 58);
expect r0 == 1 <==> 58 != 58 && 58 != 58 && 58 != 58;
}
method {:test} Test91() {
var r0 := CountEqualNumbers(58, 59, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 59;
expect r0 == 2 <==> (58 == 59 && 59 != 59) || (58 != 59 && 59 == 59) || (58 == 59 && 59 != 59);
expect r0 == 1 <==> 58 != 59 && 59 != 59 && 58 != 59;
}
method {:test} Test92() {
var r0 := CountEqualNumbers(58, 59, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 58;
expect r0 == 2 <==> (58 == 59 && 59 != 58) || (58 != 59 && 59 == 58) || (58 == 58 && 59 != 58);
expect r0 == 1 <==> 58 != 59 && 59 != 58 && 58 != 58;
}
method {:test} Test93() {
var r0 := CountEqualNumbers(58, 60, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 60 && 60 == 59;
expect r0 == 2 <==> (58 == 60 && 60 != 59) || (58 != 60 && 60 == 59) || (58 == 59 && 60 != 59);
expect r0 == 1 <==> 58 != 60 && 60 != 59 && 58 != 59;
}
method {:test} Test94() {
var r0 := CountEqualNumbers(58, 58, 59);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 58 && 58 == 59;
expect r0 == 2 <==> (58 == 58 && 58 != 59) || (58 != 58 && 58 == 59) || (58 == 59 && 58 != 59);
expect r0 == 1 <==> 58 != 58 && 58 != 59 && 58 != 59;
}

// REPEAT 10 - TIME: 262.5279267 s
