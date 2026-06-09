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

method {:test} Test25() {
var r0 := CountEqualNumbers(39, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 39 && 39 == 39;
expect r0 == 2 <==> (39 == 39 && 39 != 39) || (39 != 39 && 39 == 39) || (39 == 39 && 39 != 39);
expect r0 == 1 <==> 39 != 39 && 39 != 39 && 39 != 39;
}
method {:test} Test26() {
var r0 := CountEqualNumbers(39, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 39 && 39 == 40;
expect r0 == 2 <==> (39 == 39 && 39 != 40) || (39 != 39 && 39 == 40) || (39 == 40 && 39 != 40);
expect r0 == 1 <==> 39 != 39 && 39 != 40 && 39 != 40;
}
method {:test} Test27() {
var r0 := CountEqualNumbers(40, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 39 && 39 == 40;
expect r0 == 2 <==> (40 == 39 && 39 != 40) || (40 != 39 && 39 == 40) || (40 == 40 && 39 != 40);
expect r0 == 1 <==> 40 != 39 && 39 != 40 && 40 != 40;
}
method {:test} Test28() {
var r0 := CountEqualNumbers(39, 40, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 39 == 40 && 40 == 40;
expect r0 == 2 <==> (39 == 40 && 40 != 40) || (39 != 40 && 40 == 40) || (39 == 40 && 40 != 40);
expect r0 == 1 <==> 39 != 40 && 40 != 40 && 39 != 40;
}
method {:test} Test29() {
var r0 := CountEqualNumbers(40, 39, 41);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 40 == 39 && 39 == 41;
expect r0 == 2 <==> (40 == 39 && 39 != 41) || (40 != 39 && 39 == 41) || (40 == 41 && 39 != 41);
expect r0 == 1 <==> 40 != 39 && 39 != 41 && 40 != 41;
}

// REPEAT 6 - TIME: 25.4047856 s
