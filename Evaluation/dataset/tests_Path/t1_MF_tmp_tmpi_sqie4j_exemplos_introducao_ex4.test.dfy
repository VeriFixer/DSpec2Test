function Fat(n: nat): nat
{
   if n == 0 then 1 else n * Fat(n-1)
}

method {:testEntry} Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
    r := 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant r == Fat(i)
    {
        i := i + 1;
        r := r * i;
    }
}

method {:test} Test0() {
var r0 := Fatorial(2);
expect r0 == Fat(2);
}

// REPEAT 1 - TIME: 3.9340229 s

method {:test} Test1() {
var r0 := Fatorial(3);
expect r0 == Fat(3);
}

// REPEAT 2 - TIME: 6.5717627 s

method {:test} Test2() {
var r0 := Fatorial(4);
expect r0 == Fat(4);
}

// REPEAT 3 - TIME: 8.4171826 s

method {:test} Test3() {
var r0 := Fatorial(5);
expect r0 == Fat(5);
}

// REPEAT 4 - TIME: 10.3458591 s

method {:test} Test4() {
var r0 := Fatorial(6);
expect r0 == Fat(6);
}

// REPEAT 5 - TIME: 12.3037215 s

method {:test} Test5() {
var r0 := Fatorial(7);
expect r0 == Fat(7);
}

// REPEAT 6 - TIME: 14.3719967 s

method {:test} Test6() {
var r0 := Fatorial(8);
expect r0 == Fat(8);
}

// REPEAT 7 - TIME: 16.5344299 s

method {:test} Test7() {
var r0 := Fatorial(9);
expect r0 == Fat(9);
}

// REPEAT 8 - TIME: 18.3977152 s

method {:test} Test8() {
var r0 := Fatorial(10);
expect r0 == Fat(10);
}

// REPEAT 9 - TIME: 20.2180365 s

method {:test} Test9() {
var r0 := Fatorial(11);
expect r0 == Fat(11);
}

// REPEAT 10 - TIME: 22.1823027 s
