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
var r0 := ComputeSum(40);
expect r0 == Sum(40);
}

// REPEAT 1 - TIME: 4.2159615 s

method {:test} Test1() {
var r0 := ComputeSum(41);
expect r0 == Sum(41);
}

// REPEAT 2 - TIME: 6.9538173 s

method {:test} Test2() {
var r0 := ComputeSum(42);
expect r0 == Sum(42);
}

// REPEAT 3 - TIME: 9.1743802 s

method {:test} Test3() {
var r0 := ComputeSum(43);
expect r0 == Sum(43);
}

// REPEAT 4 - TIME: 11.7962333 s

method {:test} Test4() {
var r0 := ComputeSum(44);
expect r0 == Sum(44);
}

// REPEAT 5 - TIME: 14.4777629 s

method {:test} Test5() {
var r0 := ComputeSum(45);
expect r0 == Sum(45);
}

// REPEAT 6 - TIME: 17.0773091 s

method {:test} Test6() {
var r0 := ComputeSum(46);
expect r0 == Sum(46);
}

// REPEAT 7 - TIME: 19.6174801 s

method {:test} Test7() {
var r0 := ComputeSum(47);
expect r0 == Sum(47);
}

// REPEAT 8 - TIME: 22.320897 s

method {:test} Test8() {
var r0 := ComputeSum(48);
expect r0 == Sum(48);
}

// REPEAT 9 - TIME: 24.9424896 s

method {:test} Test9() {
var r0 := ComputeSum(49);
expect r0 == Sum(49);
}

// REPEAT 10 - TIME: 28.1731531 s
