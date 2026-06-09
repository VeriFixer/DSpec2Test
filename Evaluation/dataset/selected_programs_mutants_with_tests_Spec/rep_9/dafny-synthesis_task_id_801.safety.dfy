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

method {:test} Test40() {
var r0 := CountEqualNumbers(57, 57, 57);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 57 && 57 == 57;
expect r0 == 2 <==> (57 == 57 && 57 != 57) || (57 != 57 && 57 == 57) || (57 == 57 && 57 != 57);
expect r0 == 1 <==> 57 != 57 && 57 != 57 && 57 != 57;
}
method {:test} Test41() {
var r0 := CountEqualNumbers(57, 56, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 56 && 56 == 56;
expect r0 == 2 <==> (57 == 56 && 56 != 56) || (57 != 56 && 56 == 56) || (57 == 56 && 56 != 56);
expect r0 == 1 <==> 57 != 56 && 56 != 56 && 57 != 56;
}
method {:test} Test42() {
var r0 := CountEqualNumbers(58, 59, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 58 == 59 && 59 == 58;
expect r0 == 2 <==> (58 == 59 && 59 != 58) || (58 != 59 && 59 == 58) || (58 == 58 && 59 != 58);
expect r0 == 1 <==> 58 != 59 && 59 != 58 && 58 != 58;
}
method {:test} Test43() {
var r0 := CountEqualNumbers(57, 56, 58);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 56 && 56 == 58;
expect r0 == 2 <==> (57 == 56 && 56 != 58) || (57 != 56 && 56 == 58) || (57 == 58 && 56 != 58);
expect r0 == 1 <==> 57 != 56 && 56 != 58 && 57 != 58;
}
method {:test} Test44() {
var r0 := CountEqualNumbers(57, 57, 56);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 57 == 57 && 57 == 56;
expect r0 == 2 <==> (57 == 57 && 57 != 56) || (57 != 57 && 57 == 56) || (57 == 56 && 57 != 56);
expect r0 == 1 <==> 57 != 57 && 57 != 56 && 57 != 56;
}

// REPEAT 9 - TIME: 136.501303 s
