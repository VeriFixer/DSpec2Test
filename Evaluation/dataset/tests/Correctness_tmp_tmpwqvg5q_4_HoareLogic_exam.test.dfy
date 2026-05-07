// Redo for exam

function gcd(a: nat, b: nat): nat

lemma r1(a: nat)
    ensures gcd(a, 0) == a

lemma r2(a:nat)
    ensures gcd(a, a) == a

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)

method {:testEntry} GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
    decreases b
{
    if a < b {
        r3(a,b);
        r := GCD1(b, a);
    } else if (a % b == 0) {
        r4(a,b);
        assert b > 0;
        assert gcd(a, b) == gcd(b, a % b);
        assert a % b == 0;
        assert gcd(a, b) == gcd(b, 0);
        r1(b);
        assert gcd(a, b) == b;
        r := b;
        assert gcd(a,b) == r;
    } else {
        r4(a,b);
        r := GCD1(b, a % b);
        assert gcd(a,b) == r;
    }
    assert gcd(a,b) == r;
}

method {:testEntry} GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    decreases b
    ensures gcd(a,b) == r
{
    r1(a);
    r4(a,b);
    assert
        ( b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a) )
        &&
        ( (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b))) );
    assert
        b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a);
    assert
        b == 0 ==> a > 0 && b >= 0 && gcd(a,b) == a;
    assert
        (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b)));
    assert
        b >= 0 && b != 0 ==> b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
    if b == 0 {
        r1(a);
        assert
            gcd(a,b) == a;
        r := a;
        assert
            gcd(a,b) == r;
    } else {
        r4(a,b);
        // Method call rule
        assert
            b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
        // assert
        //    gcd(a,b) == GCD2(b, a % b);
        r := GCD2(b, a % b);
        assert
            gcd(a,b) == r;
    }
    assert
        gcd(a,b) == r;
}

method {:test} Test0() {
expect 1 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD1(1, 2);
expect gcd(1, 2) == r0;
}
method {:test} Test1() {
expect 3 > 0 && 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD1(3, 2);
expect gcd(3, 2) == r0;
}
method {:test} Test2() {
expect 2 > 0 && 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD1(2, 1);
expect gcd(2, 1) == r0;
}
method {:test} Test3() {
expect 1 > 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD2(1, 0);
expect gcd(1, 0) == r0;
}
method {:test} Test4() {
expect 5921 > 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD2(5921, 0);
expect gcd(5921, 0) == r0;
}
method {:test} Test5() {
expect 6284 > 0 && 6820 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := GCD2(6284, 6820);
expect gcd(6284, 6820) == r0;
}
