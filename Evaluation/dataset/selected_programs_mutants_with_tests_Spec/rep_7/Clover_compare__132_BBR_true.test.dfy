// Clover_compare.dfy

method {:testEntry} Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a == b ==> eq == true
  ensures a != b ==> eq == false
{
  if true {
    eq := true;
  } else {
    eq := false;
  }
}

method {:test} Test12() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 7 - TIME: 18.675338 s
