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
var r0 := CountEqualNumbers(45, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 45 && 45 == 45;
expect r0 == 2 <==> (45 == 45 && 45 != 45) || (45 != 45 && 45 == 45) || (45 == 45 && 45 != 45);
expect r0 == 1 <==> 45 != 45 && 45 != 45 && 45 != 45;
}
method {:test} Test36() {
var r0 := CountEqualNumbers(46, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 46 && 46 == 45;
expect r0 == 2 <==> (46 == 46 && 46 != 45) || (46 != 46 && 46 == 45) || (46 == 45 && 46 != 45);
expect r0 == 1 <==> 46 != 46 && 46 != 45 && 46 != 45;
}
method {:test} Test37() {
var r0 := CountEqualNumbers(45, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 45 == 46 && 46 == 45;
expect r0 == 2 <==> (45 == 46 && 46 != 45) || (45 != 46 && 46 == 45) || (45 == 45 && 46 != 45);
expect r0 == 1 <==> 45 != 46 && 46 != 45 && 45 != 45;
}
method {:test} Test38() {
var r0 := CountEqualNumbers(46, 45, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 46 == 45 && 45 == 45;
expect r0 == 2 <==> (46 == 45 && 45 != 45) || (46 != 45 && 45 == 45) || (46 == 45 && 45 != 45);
expect r0 == 1 <==> 46 != 45 && 45 != 45 && 46 != 45;
}
method {:test} Test39() {
var r0 := CountEqualNumbers(47, 46, 45);
expect r0 >= 0 && r0 <= 3;
expect r0 == 3 <==> 47 == 46 && 46 == 45;
expect r0 == 2 <==> (47 == 46 && 46 != 45) || (47 != 46 && 46 == 45) || (47 == 45 && 46 != 45);
expect r0 == 1 <==> 47 != 46 && 46 != 45 && 47 != 45;
}

// REPEAT 8 - TIME: 33.6277669 s
