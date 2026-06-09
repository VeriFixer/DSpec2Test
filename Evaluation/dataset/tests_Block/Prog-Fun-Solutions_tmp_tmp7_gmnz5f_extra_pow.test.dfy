ghost function pow(a: int, e: nat): int {
    if e == 0 then 1 else a*pow(a, e-1)
}

method {:testEntry} Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{

    var x:nat := 1;
    var k:nat := 0;
    while k < n
    invariant x == pow(a, k)
    invariant 0 <= k <= n
    decreases n-k
    {
        assert x == pow(a, k);
        x := a*x;
        assert x == a*pow(a, k);
        assert x == pow(a, k+1);
         
        k := k + 1;
        assert x == pow(a, k);

    }
    assert k == n;
    y := x;
    assert y == pow(a, n);

}

method {:test} Test0() {
var r0 := Pow(5853, 1144);
}

// REPEAT 1 - TIME: 2.2028134 s

method {:test} Test1() {
var r0 := Pow(5854, 1145);
}

// REPEAT 2 - TIME: 3.1942934 s

method {:test} Test2() {
var r0 := Pow(5855, 1146);
}

// REPEAT 3 - TIME: 4.2348205 s

method {:test} Test3() {
var r0 := Pow(5856, 1147);
}

// REPEAT 4 - TIME: 5.1417228 s

method {:test} Test4() {
var r0 := Pow(5857, 1148);
}

// REPEAT 5 - TIME: 6.1440355 s

method {:test} Test5() {
var r0 := Pow(5858, 1149);
}

// REPEAT 6 - TIME: 6.9100585 s

method {:test} Test6() {
var r0 := Pow(5859, 1150);
}

// REPEAT 7 - TIME: 7.7021263 s

method {:test} Test7() {
var r0 := Pow(5860, 1151);
}

// REPEAT 8 - TIME: 8.454397 s

method {:test} Test8() {
var r0 := Pow(5861, 1152);
}

// REPEAT 9 - TIME: 9.163123 s

method {:test} Test9() {
var r0 := Pow(5862, 1153);
}

// REPEAT 10 - TIME: 9.8406286 s
