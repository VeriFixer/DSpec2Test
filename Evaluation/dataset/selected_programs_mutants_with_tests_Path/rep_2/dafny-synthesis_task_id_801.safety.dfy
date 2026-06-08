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
var r0 := CountEqualNumbers(28, 28, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 28 && 28 == 28;
expect r0 == 2 <==> (28 == 28 && 28 != 28) || (28 != 28 && 28 == 28) || (28 == 28 && 28 != 28);
expect r0 == 1 <==> 28 != 28 && 28 != 28 && 28 != 28;
}
method {:test} Test6() {
var r0 := CountEqualNumbers(28, 28, 29);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 28 && 28 == 29;
expect r0 == 2 <==> (28 == 28 && 28 != 29) || (28 != 28 && 28 == 29) || (28 == 29 && 28 != 29);
expect r0 == 1 <==> 28 != 28 && 28 != 29 && 28 != 29;
}
method {:test} Test7() {
var r0 := CountEqualNumbers(28, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 28 == 27 && 27 == 28;
expect r0 == 2 <==> (28 == 27 && 27 != 28) || (28 != 27 && 27 == 28) || (28 == 28 && 27 != 28);
expect r0 == 1 <==> 28 != 27 && 27 != 28 && 28 != 28;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(29, 27, 27);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 27 && 27 == 27;
expect r0 == 2 <==> (29 == 27 && 27 != 27) || (29 != 27 && 27 == 27) || (29 == 27 && 27 != 27);
expect r0 == 1 <==> 29 != 27 && 27 != 27 && 29 != 27;
}
method {:test} Test9() {
var r0 := CountEqualNumbers(29, 27, 28);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 29 == 27 && 27 == 28;
expect r0 == 2 <==> (29 == 27 && 27 != 28) || (29 != 27 && 27 == 28) || (29 == 28 && 27 != 28);
expect r0 == 1 <==> 29 != 27 && 27 != 28 && 29 != 28;
}

// REPEAT 2 - TIME: 15.8930798 s
