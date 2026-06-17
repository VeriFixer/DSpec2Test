// MIEIC_mfes_tmp_tmpq3ho7nve_exams_mt2_19_p4.dfy

function R(n: nat): nat
{
  if n == 0 then
    0
  else if R(n - 1) > n then
    R(n - 1) - n
  else
    R(n - 1) + n
}

method {:testEntry} calcR(n: nat) returns (r: nat)
  ensures r == R(n)
{
  r := 0;
  var i := 0;
  while i == n
    invariant 0 <= i <= n
    invariant r == R(i)
    decreases n - i
  {
    i := i + 1;
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
  }
}


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

// REPEAT 1 - TIME: 2.2323318 s

method {:test} Test1() {
var r0 := calcR(2);
expect r0 == R(2);
}

// REPEAT 2 - TIME: 3.2071043 s

method {:test} Test2() {
var r0 := calcR(3);
expect r0 == R(3);
}

// REPEAT 3 - TIME: 4.1242327 s

method {:test} Test3() {
var r0 := calcR(4);
expect r0 == R(4);
}

// REPEAT 4 - TIME: 5.0756965 s

method {:test} Test4() {
var r0 := calcR(5);
expect r0 == R(5);
}

// REPEAT 5 - TIME: 6.1272468 s

method {:test} Test5() {
var r0 := calcR(6);
expect r0 == R(6);
}

// REPEAT 6 - TIME: 7.0684058 s

method {:test} Test6() {
var r0 := calcR(7);
expect r0 == R(7);
}

// REPEAT 7 - TIME: 7.9075954 s

method {:test} Test7() {
var r0 := calcR(8);
expect r0 == R(8);
}

// REPEAT 8 - TIME: 8.7234202 s

method {:test} Test8() {
var r0 := calcR(9);
expect r0 == R(9);
}

// REPEAT 9 - TIME: 9.5734145 s

method {:test} Test9() {
var r0 := calcR(10);
expect r0 == R(10);
}

// REPEAT 10 - TIME: 10.3510819 s
