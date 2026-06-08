function Sum(n:nat):nat
 
{
  if n==0 then  0 else n + Sum(n-1)
}

method {:testEntry} ComputeSum(n:nat) returns (s:nat)
    ensures s ==Sum(n)
{
    s := 0;
    var i := 0;
    while i< n
      invariant 0 <= i <= n
      invariant s == Sum(i)
      {
        s := s + i + 1;
        i := i+1;
      }
}

method {:test} Test0() {
var r0 := ComputeSum(7721);
expect r0 == Sum(7721);
}
method {:test} Test1() {
var r0 := ComputeSum(100);
expect r0 == Sum(100);
}
method {:test} Test3() {
var r0 := ComputeSum(24);
expect r0 == Sum(24);
}

// REPEAT 1 - TIME: 5.2535892 s

method {:test} Test6() {
var r0 := ComputeSum(7722);
expect r0 == Sum(7722);
}

// REPEAT 2 - TIME: 5.9746445 s

method {:test} Test7() {
var r0 := ComputeSum(7723);
expect r0 == Sum(7723);
}

// REPEAT 3 - TIME: 6.5945214 s

method {:test} Test8() {
var r0 := ComputeSum(7724);
expect r0 == Sum(7724);
}

// REPEAT 4 - TIME: 7.2015932 s

method {:test} Test9() {
var r0 := ComputeSum(7725);
expect r0 == Sum(7725);
}

// REPEAT 5 - TIME: 7.7206401 s

method {:test} Test10() {
var r0 := ComputeSum(7726);
expect r0 == Sum(7726);
}

// REPEAT 6 - TIME: 8.244541 s

method {:test} Test11() {
var r0 := ComputeSum(7727);
expect r0 == Sum(7727);
}

// REPEAT 7 - TIME: 8.7096929 s

method {:test} Test12() {
var r0 := ComputeSum(7728);
expect r0 == Sum(7728);
}

// REPEAT 8 - TIME: 9.1790345 s

method {:test} Test13() {
var r0 := ComputeSum(7729);
expect r0 == Sum(7729);
}

// REPEAT 9 - TIME: 9.6577416 s

method {:test} Test14() {
var r0 := ComputeSum(7730);
expect r0 == Sum(7730);
}

// REPEAT 10 - TIME: 10.032179 s
