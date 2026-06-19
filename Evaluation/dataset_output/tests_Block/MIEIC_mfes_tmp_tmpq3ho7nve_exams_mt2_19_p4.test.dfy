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
var r0 := calcR(1);
expect r0 == R(1);
}

// REPEAT 1 - TIME: 2.3142776 s

method {:test} Test1() {
var r0 := calcR(2);
expect r0 == R(2);
}

// REPEAT 2 - TIME: 3.2868028 s

method {:test} Test2() {
var r0 := calcR(3);
expect r0 == R(3);
}

// REPEAT 3 - TIME: 4.0486462 s

method {:test} Test3() {
var r0 := calcR(4);
expect r0 == R(4);
}

// REPEAT 4 - TIME: 4.7865148 s

method {:test} Test4() {
var r0 := calcR(5);
expect r0 == R(5);
}

// REPEAT 5 - TIME: 5.5559024 s

method {:test} Test5() {
var r0 := calcR(6);
expect r0 == R(6);
}

// REPEAT 6 - TIME: 6.3027751 s

method {:test} Test6() {
var r0 := calcR(7);
expect r0 == R(7);
}

// REPEAT 7 - TIME: 7.0531142 s

method {:test} Test7() {
var r0 := calcR(8);
expect r0 == R(8);
}

// REPEAT 8 - TIME: 7.6132171 s

method {:test} Test8() {
var r0 := calcR(9);
expect r0 == R(9);
}

// REPEAT 9 - TIME: 8.1818914 s

method {:test} Test9() {
var r0 := calcR(10);
expect r0 == R(10);
}

// REPEAT 10 - TIME: 8.7984465 s
