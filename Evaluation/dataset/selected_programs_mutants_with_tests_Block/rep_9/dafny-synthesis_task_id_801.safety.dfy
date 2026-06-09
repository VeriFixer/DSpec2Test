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

method {:test} Test18() {
var r0 := CountEqualNumbers(43, 44, 44);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 44 && 44 == 44;
expect r0 == 2 <==> (43 == 44 && 44 != 44) || (43 != 44 && 44 == 44) || (43 == 44 && 44 != 44);
expect r0 == 1 <==> 43 != 44 && 44 != 44 && 43 != 44;
}
method {:test} Test19() {
var r0 := CountEqualNumbers(43, 43, 43);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 43 == 43 && 43 == 43;
expect r0 == 2 <==> (43 == 43 && 43 != 43) || (43 != 43 && 43 == 43) || (43 == 43 && 43 != 43);
expect r0 == 1 <==> 43 != 43 && 43 != 43 && 43 != 43;
}

// REPEAT 9 - TIME: 12.2252852 s
