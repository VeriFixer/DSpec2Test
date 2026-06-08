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

method {:test} Test7() {
var r0 := CountEqualNumbers(33, 32, 32);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 32 && 32 == 32;
expect r0 == 2 <==> (33 == 32 && 32 != 32) || (33 != 32 && 32 == 32) || (33 == 32 && 32 != 32);
expect r0 == 1 <==> 33 != 32 && 32 != 32 && 33 != 32;
}
method {:test} Test8() {
var r0 := CountEqualNumbers(33, 33, 33);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 33 == 33 && 33 == 33;
expect r0 == 2 <==> (33 == 33 && 33 != 33) || (33 != 33 && 33 == 33) || (33 == 33 && 33 != 33);
expect r0 == 1 <==> 33 != 33 && 33 != 33 && 33 != 33;
}

// REPEAT 4 - TIME: 7.0105091 s
