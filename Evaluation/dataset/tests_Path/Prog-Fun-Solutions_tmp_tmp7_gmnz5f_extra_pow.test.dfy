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
var r0 := Pow(0, 8100);
}

// REPEAT 1 - TIME: 7.7590492 s

method {:test} Test1() {
var r0 := Pow(1, 8101);
}

// REPEAT 2 - TIME: 12.4499293 s

method {:test} Test2() {
var r0 := Pow(2, 8102);
}

// REPEAT 3 - TIME: 16.0839365 s

method {:test} Test3() {
var r0 := Pow(3, 8103);
}

// REPEAT 4 - TIME: 20.2948016 s

method {:test} Test4() {
var r0 := Pow(4, 8104);
}

// REPEAT 5 - TIME: 24.3360377 s

method {:test} Test5() {
var r0 := Pow(5, 8105);
}

// REPEAT 6 - TIME: 27.9525929 s

method {:test} Test6() {
var r0 := Pow(287, 8106);
}

// REPEAT 7 - TIME: 31.6688738 s

method {:test} Test7() {
var r0 := Pow(288, 8107);
}

// REPEAT 8 - TIME: 35.4949005 s

method {:test} Test8() {
var r0 := Pow(289, 8108);
}

// REPEAT 9 - TIME: 39.516742 s

method {:test} Test9() {
var r0 := Pow(290, 8109);
}

// REPEAT 10 - TIME: 43.7497127 s
