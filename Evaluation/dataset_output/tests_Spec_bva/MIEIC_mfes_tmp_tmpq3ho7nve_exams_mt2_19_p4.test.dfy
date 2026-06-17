function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

method {:testEntry} calcR(n: nat) returns (r: nat)
    ensures r == R(n) 
{
    r := 0;
    var i := 0;
    while i < n 
        decreases n-i
        invariant 0 <= i <= n
        invariant r == R(i)
    {
       i := i + 1;
       if r  > i {
           r := r - i;
       } 
       else {
            r := r + i;
        }
    }
}

method {:test} Test0() {
var r0 := calcR(7721);
expect r0 == R(7721);
}
method {:test} Test1() {
var r0 := calcR(100);
expect r0 == R(100);
}

// REPEAT 1 - TIME: 5.9144516 s

method {:test} Test6() {
var r0 := calcR(7722);
expect r0 == R(7722);
}

// REPEAT 2 - TIME: 6.7435816 s

method {:test} Test7() {
var r0 := calcR(7723);
expect r0 == R(7723);
}

// REPEAT 3 - TIME: 7.7575759 s

method {:test} Test8() {
var r0 := calcR(7724);
expect r0 == R(7724);
}

// REPEAT 4 - TIME: 8.7039991 s

method {:test} Test9() {
var r0 := calcR(7725);
expect r0 == R(7725);
}

// REPEAT 5 - TIME: 9.469461 s

method {:test} Test10() {
var r0 := calcR(7726);
expect r0 == R(7726);
}

// REPEAT 6 - TIME: 10.1699279 s

method {:test} Test11() {
var r0 := calcR(7727);
expect r0 == R(7727);
}

// REPEAT 7 - TIME: 11.0747228 s

method {:test} Test12() {
var r0 := calcR(7728);
expect r0 == R(7728);
}

// REPEAT 8 - TIME: 11.8275992 s

method {:test} Test13() {
var r0 := calcR(7729);
expect r0 == R(7729);
}

// REPEAT 9 - TIME: 12.4609656 s

method {:test} Test14() {
var r0 := calcR(7730);
expect r0 == R(7730);
}

// REPEAT 10 - TIME: 12.9647932 s
