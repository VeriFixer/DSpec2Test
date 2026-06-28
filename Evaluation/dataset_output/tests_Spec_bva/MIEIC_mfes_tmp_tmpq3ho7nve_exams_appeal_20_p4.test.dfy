function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

method {:testEntry} calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i < n
    decreases n-i
    invariant 0 <= i <= n
    invariant a == F(i) && b == F(i+1) && c == F(i+2)
   {
    a, b, c := b, c, a + c;        
    i := i + 1;
  }
  res := a;
}

method {:test} Test0() {
var r0 := calcF(2);
expect r0 == F(2);
}
method {:test} Test1() {
var r0 := calcF(100);
expect r0 == F(100);
}
method {:test} Test3() {
var r0 := calcF(1802);
expect r0 == F(1802);
}
method {:test} Test4() {
var r0 := calcF(1242);
expect r0 == F(1242);
}

// REPEAT 1 - TIME: 8.551345 s

method {:test} Test6() {
var r0 := calcF(1803);
expect r0 == F(1803);
}

// REPEAT 2 - TIME: 9.7431885 s

method {:test} Test7() {
var r0 := calcF(1804);
expect r0 == F(1804);
}

// REPEAT 3 - TIME: 10.633822 s

method {:test} Test8() {
var r0 := calcF(1805);
expect r0 == F(1805);
}

// REPEAT 4 - TIME: 11.4917442 s

method {:test} Test9() {
var r0 := calcF(1806);
expect r0 == F(1806);
}

// REPEAT 5 - TIME: 12.3386545 s

method {:test} Test10() {
var r0 := calcF(1807);
expect r0 == F(1807);
}

// REPEAT 6 - TIME: 13.1929684 s

method {:test} Test11() {
var r0 := calcF(1808);
expect r0 == F(1808);
}

// REPEAT 7 - TIME: 14.0564033 s

method {:test} Test12() {
var r0 := calcF(1809);
expect r0 == F(1809);
}

// REPEAT 8 - TIME: 15.0445941 s

method {:test} Test13() {
var r0 := calcF(1810);
expect r0 == F(1810);
}

// REPEAT 9 - TIME: 16.0535942 s

method {:test} Test14() {
var r0 := calcF(1811);
expect r0 == F(1811);
}

// REPEAT 10 - TIME: 17.0084182 s
