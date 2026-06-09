// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

ghost function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}

method {:testEntry} problem5(n:nat) returns (x: int)
ensures x == f(n)
{

    var a := 1;
    var b := 0;
    var k := n;
    while k >= 0
    invariant f(n) == a*f(k) + b
    invariant -5 <= k <= n
    decreases k
    {
        assert f(n) == a*f(k) + b;
        assert f(n) == a*(3*f(k-5)+k) + b;

        assert f(n) == 3*a*f(k-5) + a*k + b;
        b := a*k + b;
        assert f(n) == 3*a*f(k-5) + b;
        a := 3*a;
        assert f(n) == a*f(k-5) + b;
        k := k - 5;
        assert f(n) == a*f(k) + b;
    }
    
    assert k < 0;
    assert f(n) == a*f(k) + b;
    assert f(n) == a*0 + b;
    x := b;
    assert x== f(n);

}

method {:test} Test0() {
var r0 := problem5(1);
}

// REPEAT 1 - TIME: 7.0321259 s

method {:test} Test1() {
var r0 := problem5(2);
}

// REPEAT 2 - TIME: 11.4078842 s

method {:test} Test2() {
var r0 := problem5(3);
}

// REPEAT 3 - TIME: 14.9701332 s

method {:test} Test3() {
var r0 := problem5(4);
}

// REPEAT 4 - TIME: 18.2975898 s

method {:test} Test4() {
var r0 := problem5(1801);
}

// REPEAT 5 - TIME: 21.6906653 s

method {:test} Test5() {
var r0 := problem5(1803);
}

// REPEAT 6 - TIME: 25.0973984 s

method {:test} Test6() {
var r0 := problem5(1806);
}

// REPEAT 7 - TIME: 28.2560248 s

method {:test} Test7() {
var r0 := problem5(1809);
}

// REPEAT 8 - TIME: 31.6106112 s

method {:test} Test8() {
var r0 := problem5(1812);
}

// REPEAT 9 - TIME: 34.938937 s

method {:test} Test9() {
var r0 := problem5(1815);
}

// REPEAT 10 - TIME: 38.6950115 s
