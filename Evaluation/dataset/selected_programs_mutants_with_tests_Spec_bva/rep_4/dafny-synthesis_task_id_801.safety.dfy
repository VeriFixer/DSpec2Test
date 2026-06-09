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

method {:test} Test60() {
var r0 := CountEqualNumbers(37, 37, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 37 && 37 == 37;
expect r0 == 2 <==> (37 == 37 && 37 != 37) || (37 != 37 && 37 == 37) || (37 == 37 && 37 != 37);
expect r0 == 1 <==> 37 != 37 && 37 != 37 && 37 != 37;
}
method {:test} Test61() {
var r0 := CountEqualNumbers(38, 39, 39);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 39 && 39 == 39;
expect r0 == 2 <==> (38 == 39 && 39 != 39) || (38 != 39 && 39 == 39) || (38 == 39 && 39 != 39);
expect r0 == 1 <==> 38 != 39 && 39 != 39 && 38 != 39;
}
method {:test} Test62() {
var r0 := CountEqualNumbers(37, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 37 == 36 && 36 == 37;
expect r0 == 2 <==> (37 == 36 && 36 != 37) || (37 != 36 && 36 == 37) || (37 == 37 && 36 != 37);
expect r0 == 1 <==> 37 != 36 && 36 != 37 && 37 != 37;
}
method {:test} Test63() {
var r0 := CountEqualNumbers(38, 39, 40);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 38 == 39 && 39 == 40;
expect r0 == 2 <==> (38 == 39 && 39 != 40) || (38 != 39 && 39 == 40) || (38 == 40 && 39 != 40);
expect r0 == 1 <==> 38 != 39 && 39 != 40 && 38 != 40;
}
method {:test} Test64() {
var r0 := CountEqualNumbers(36, 36, 37);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 36 == 36 && 36 == 37;
expect r0 == 2 <==> (36 == 36 && 36 != 37) || (36 != 36 && 36 == 37) || (36 == 37 && 36 != 37);
expect r0 == 1 <==> 36 != 36 && 36 != 37 && 36 != 37;
}

// REPEAT 4 - TIME: 207.2685895 s
