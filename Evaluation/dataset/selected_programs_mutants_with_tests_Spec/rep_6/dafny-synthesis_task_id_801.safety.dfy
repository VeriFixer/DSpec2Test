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
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test26() {
var r0 := CountEqualNumbers(45, 46, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 46;
expect r0 == 2 <==> (45 == 46 && 46 != 46) || (45 != 46 && 46 == 46) || (45 == 46 && 46 != 46);
expect r0 == 1 <==> 45 != 46 && 46 != 46 && 45 != 46;
}
method {:test} Test27() {
var r0 := CountEqualNumbers(45, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 44 && 44 == 45;
expect r0 == 2 <==> (45 == 44 && 44 != 45) || (45 != 44 && 44 == 45) || (45 == 45 && 44 != 45);
expect r0 == 1 <==> 45 != 44 && 44 != 45 && 45 != 45;
}
method {:test} Test28() {
var r0 := CountEqualNumbers(45, 46, 47);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 47;
expect r0 == 2 <==> (45 == 46 && 46 != 47) || (45 != 46 && 46 == 47) || (45 == 47 && 46 != 47);
expect r0 == 1 <==> 45 != 46 && 46 != 47 && 45 != 47;
}
method {:test} Test29() {
var r0 := CountEqualNumbers(44, 44, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 44 == 44 && 44 == 45;
expect r0 == 2 <==> (44 == 44 && 44 != 45) || (44 != 44 && 44 == 45) || (44 == 45 && 44 != 45);
expect r0 == 1 <==> 44 != 44 && 44 != 45 && 44 != 45;
}

// REPEAT 6 - TIME: 90.5346808 s
