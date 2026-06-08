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

method {:test} Test35() {
var r0 := CountEqualNumbers(52, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 52;
expect r0 == 2 <==> (52 == 52 && 52 != 52) || (52 != 52 && 52 == 52) || (52 == 52 && 52 != 52);
expect r0 == 1 <==> 52 != 52 && 52 != 52 && 52 != 52;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(53, 52, 52);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 52 && 52 == 52;
expect r0 == 2 <==> (53 == 52 && 52 != 52) || (53 != 52 && 52 == 52) || (53 == 52 && 52 != 52);
expect r0 == 1 <==> 53 != 52 && 52 != 52 && 53 != 52;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(53, 54, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 53;
expect r0 == 2 <==> (53 == 54 && 54 != 53) || (53 != 54 && 54 == 53) || (53 == 53 && 54 != 53);
expect r0 == 1 <==> 53 != 54 && 54 != 53 && 53 != 53;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(53, 54, 55);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 53 == 54 && 54 == 55;
expect r0 == 2 <==> (53 == 54 && 54 != 55) || (53 != 54 && 54 == 55) || (53 == 55 && 54 != 55);
expect r0 == 1 <==> 53 != 54 && 54 != 55 && 53 != 55;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(52, 52, 53);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 52 == 52 && 52 == 53;
expect r0 == 2 <==> (52 == 52 && 52 != 53) || (52 != 52 && 52 == 53) || (52 == 53 && 52 != 53);
expect r0 == 1 <==> 52 != 52 && 52 != 53 && 52 != 53;
}

// REPEAT 8 - TIME: 107.1421186 s
