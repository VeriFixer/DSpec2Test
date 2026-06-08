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

// REPEAT 1 - TIME: 3.9329302 s

method {:test} Test2() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 2 - TIME: 5.9414075 s

method {:test} Test4() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 3 - TIME: 7.4644864 s

method {:test} Test6() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 4 - TIME: 9.0811579 s

method {:test} Test8() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 5 - TIME: 10.6847821 s

method {:test} Test10() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 6 - TIME: 12.1439006 s

method {:test} Test12() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 7 - TIME: 13.351671 s

method {:test} Test14() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 8 - TIME: 14.7818145 s

method {:test} Test16() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 9 - TIME: 16.1346592 s

method {:test} Test18() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 10 - TIME: 17.3827475 s
