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
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}
method {:test} Test11() {
var r0 := CountEqualNumbers(34, 35, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 35 && 35 == 35;
expect r0 == 2 <==> (34 == 35 && 35 != 35) || (34 != 35 && 35 == 35) || (34 == 35 && 35 != 35);
expect r0 == 1 <==> 34 != 35 && 35 != 35 && 34 != 35;
}
method {:test} Test12() {
var r0 := CountEqualNumbers(33, 24, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 24 && 24 == 33;
expect r0 == 2 <==> (33 == 24 && 24 != 33) || (33 != 24 && 24 == 33) || (33 == 33 && 24 != 33);
expect r0 == 1 <==> 33 != 24 && 24 != 33 && 33 != 33;
}
method {:test} Test13() {
var r0 := CountEqualNumbers(33, 24, 34);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 24 && 24 == 34;
expect r0 == 2 <==> (33 == 24 && 24 != 34) || (33 != 24 && 24 == 34) || (33 == 34 && 24 != 34);
expect r0 == 1 <==> 33 != 24 && 24 != 34 && 33 != 34;
}
method {:test} Test14() {
var r0 := CountEqualNumbers(34, 34, 35);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 34 == 34 && 34 == 35;
expect r0 == 2 <==> (34 == 34 && 34 != 35) || (34 != 34 && 34 == 35) || (34 == 35 && 34 != 35);
expect r0 == 1 <==> 34 != 34 && 34 != 35 && 34 != 35;
}

// REPEAT 3 - TIME: 65.7353107 s
