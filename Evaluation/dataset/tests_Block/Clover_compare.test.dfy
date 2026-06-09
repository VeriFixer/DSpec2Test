method {:testEntry} Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a==b ==> eq==true
  ensures a!=b ==> eq==false
{
  if a == b { eq := true; } else { eq := false; }
}

method {:test} Test0() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 1 - TIME: 2.0015061 s

method {:test} Test2() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 2 - TIME: 2.7832334 s

method {:test} Test4() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 3 - TIME: 3.758549 s

method {:test} Test6() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 4 - TIME: 4.710964 s

method {:test} Test8() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 5 - TIME: 5.7960647 s

method {:test} Test10() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 6 - TIME: 6.7262972 s

method {:test} Test12() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 7 - TIME: 7.5067322 s

method {:test} Test14() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 8 - TIME: 8.4213089 s

method {:test} Test16() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 9 - TIME: 9.2275829 s

method {:test} Test18() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 10 - TIME: 10.0108601 s
