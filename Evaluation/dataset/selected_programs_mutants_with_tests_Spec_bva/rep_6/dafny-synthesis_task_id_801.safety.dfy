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

method {:test} Test70() {
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test71() {
var r0 := CountEqualNumbers(46, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 45;
expect r0 == 2 <==> (46 == 45 && 45 != 45) || (46 != 45 && 45 == 45) || (46 == 45 && 45 != 45);
expect r0 == 1 <==> 46 != 45 && 45 != 45 && 46 != 45;
}
method {:test} Test72() {
var r0 := CountEqualNumbers(46, 45, 46);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 46;
expect r0 == 2 <==> (46 == 45 && 45 != 46) || (46 != 45 && 45 == 46) || (46 == 46 && 45 != 46);
expect r0 == 1 <==> 46 != 45 && 45 != 46 && 46 != 46;
}
method {:test} Test73() {
var r0 := CountEqualNumbers(46, 47, 48);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 47 && 47 == 48;
expect r0 == 2 <==> (46 == 47 && 47 != 48) || (46 != 47 && 47 == 48) || (46 == 48 && 47 != 48);
expect r0 == 1 <==> 46 != 47 && 47 != 48 && 46 != 48;
}
method {:test} Test74() {
var r0 := CountEqualNumbers(46, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 45;
expect r0 == 2 <==> (46 == 46 && 46 != 45) || (46 != 46 && 46 == 45) || (46 == 45 && 46 != 45);
expect r0 == 1 <==> 46 != 46 && 46 != 45 && 46 != 45;
}

// REPEAT 6 - TIME: 225.6194709 s
